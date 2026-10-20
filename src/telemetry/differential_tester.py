"""Differential testing: the C++/CUDA runtime vs. PyTorch reference implementations.

The runtime is loaded through its C ABI (``glimmer_runtime.h``) with ctypes, so the same tests run
against the CUDA build and the CPU_FALLBACK build. The references implement vLLM's paged-KV
semantics directly in PyTorch: ``slot_mapping = block_table[req, pos // 16] * 16 + pos % 16``
(as consumed by ``reshape_and_cache``) and a row gather from the flattened cache.

    python -m src.telemetry.differential_tester            # runs tests/test_differential.py
    GLIMMER_RUNTIME_LIB=/path/to/libglimmer_runtime.so ...  # pick a specific build
"""

from __future__ import annotations

import ctypes
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[2]
LIBRARY_NAMES = ("libglimmer_runtime.so", "libglimmer_runtime.dylib", "libglimmer_runtime.dll", "glimmer_runtime.dll")
BLOCK_SIZE = 16

GLIMMER_OK = 0
_STATUS_NAMES = {1: "invalid argument", 2: "CUDA error", 3: "out of memory", 4: "internal error"}

_i32p = ctypes.POINTER(ctypes.c_int32)
_i64p = ctypes.POINTER(ctypes.c_int64)
_f32p = ctypes.POINTER(ctypes.c_float)


class GlimmerRuntimeError(RuntimeError):
    def __init__(self, status: int, message: str) -> None:
        super().__init__(f"{_STATUS_NAMES.get(status, f'status {status}')}: {message}")
        self.status = status


def find_runtime_library(explicit: str | os.PathLike[str] | None = None) -> Path:
    explicit = explicit or os.environ.get("GLIMMER_RUNTIME_LIB")
    if explicit:
        path = Path(explicit)
        if not path.is_file():
            raise FileNotFoundError(f"GLIMMER_RUNTIME_LIB={path} does not exist")
        return path
    candidates = [p for d in sorted(REPO_ROOT.glob("build*")) for name in LIBRARY_NAMES for p in d.rglob(name)]
    if not candidates:
        raise FileNotFoundError(
            "glimmer runtime library not found under build*/; run `make runtime CPU_FALLBACK=1` "
            "or `cmake -S . -B build -DCPU_FALLBACK=ON && cmake --build build`"
        )
    return max(candidates, key=lambda p: p.stat().st_mtime)


def _ptr(array: np.ndarray, ctype: type) -> ctypes._Pointer:
    return array.ctypes.data_as(ctype)


class GlimmerRuntime:
    def __init__(self, path: str | os.PathLike[str] | None = None) -> None:
        self.path = find_runtime_library(path)
        if sys.platform == "win32":
            os.add_dll_directory(str(self.path.parent))
            cuda_bin = Path(os.environ.get("CUDA_PATH", "")) / "bin"
            if cuda_bin.is_dir():
                os.add_dll_directory(str(cuda_bin))
        lib = ctypes.CDLL(str(self.path))

        lib.glimmer_backend_name.restype = ctypes.c_char_p
        lib.glimmer_last_error.restype = ctypes.c_char_p
        lib.glimmer_kv_block_size.restype = ctypes.c_int32
        lib.glimmer_live_device_bytes.restype = ctypes.c_int64
        lib.glimmer_live_pinned_bytes.restype = ctypes.c_int64
        index_args = [_i32p, ctypes.c_int32, ctypes.c_int32, ctypes.c_int32, _i32p, _i32p, ctypes.c_int32, _i64p]
        for name in ("glimmer_paged_kv_index", "glimmer_paged_kv_index_zero_copy"):
            fn = getattr(lib, name)
            fn.argtypes = index_args
            fn.restype = ctypes.c_int
        lib.glimmer_paged_kv_gather.argtypes = [_f32p, ctypes.c_int32, ctypes.c_int32, _i64p, ctypes.c_int32, _f32p]
        lib.glimmer_paged_kv_gather.restype = ctypes.c_int
        self._lib = lib

        if lib.glimmer_kv_block_size() != BLOCK_SIZE:
            raise RuntimeError(f"runtime block size {lib.glimmer_kv_block_size()} != {BLOCK_SIZE}")

    @property
    def backend(self) -> str:
        return self._lib.glimmer_backend_name().decode()

    def live_device_bytes(self) -> int:
        return int(self._lib.glimmer_live_device_bytes())

    def live_pinned_bytes(self) -> int:
        return int(self._lib.glimmer_live_pinned_bytes())

    def _check(self, status: int) -> None:
        if status != GLIMMER_OK:
            raise GlimmerRuntimeError(status, self._lib.glimmer_last_error().decode(errors="replace"))

    def paged_kv_index(
        self,
        block_tables: np.ndarray,
        req_ids: np.ndarray,
        token_pos: np.ndarray,
        num_physical_blocks: int,
        *,
        zero_copy: bool = False,
    ) -> np.ndarray:
        tables = np.ascontiguousarray(block_tables, dtype=np.int32)
        if tables.ndim != 2:
            raise ValueError("block_tables must be 2-D [num_reqs, max_blocks_per_req]")
        req = np.ascontiguousarray(req_ids, dtype=np.int32).reshape(-1)
        pos = np.ascontiguousarray(token_pos, dtype=np.int32).reshape(-1)
        if req.shape != pos.shape:
            raise ValueError("req_ids and token_pos must have the same length")
        out = np.empty(req.shape[0], dtype=np.int64)
        fn = self._lib.glimmer_paged_kv_index_zero_copy if zero_copy else self._lib.glimmer_paged_kv_index
        self._check(fn(_ptr(tables, _i32p), tables.shape[0], tables.shape[1], int(num_physical_blocks),
                       _ptr(req, _i32p), _ptr(pos, _i32p), req.shape[0], _ptr(out, _i64p)))
        return out

    def paged_kv_gather(self, kv_cache: np.ndarray, slots: np.ndarray) -> np.ndarray:
        """``kv_cache`` is [num_physical_blocks, 16, *row_shape]; returns [n_slots, *row_shape]."""
        cache = np.ascontiguousarray(kv_cache, dtype=np.float32)
        if cache.ndim < 3 or cache.shape[1] != BLOCK_SIZE:
            raise ValueError(f"kv_cache must be [num_blocks, {BLOCK_SIZE}, ...]")
        row_shape = cache.shape[2:]
        row_elems = int(np.prod(row_shape))
        idx = np.ascontiguousarray(slots, dtype=np.int64).reshape(-1)
        out = np.empty((idx.shape[0], row_elems), dtype=np.float32)
        self._check(self._lib.glimmer_paged_kv_gather(_ptr(cache, _f32p), cache.shape[0], row_elems,
                                                      _ptr(idx, _i64p), idx.shape[0], _ptr(out, _f32p)))
        return out.reshape((idx.shape[0], *row_shape))


# ---------------------------------------------------------------------------
# PyTorch references
# ---------------------------------------------------------------------------

def reference_paged_kv_index(block_tables, req_ids, token_pos, num_physical_blocks: int, block_size: int = BLOCK_SIZE):
    import torch

    tables = block_tables.to(torch.int64)
    req = req_ids.to(torch.int64)
    pos = token_pos.to(torch.int64)
    num_reqs, max_blocks = tables.shape
    logical = torch.div(pos, block_size, rounding_mode="floor")
    valid = (req >= 0) & (req < num_reqs) & (pos >= 0) & (logical < max_blocks)
    if num_reqs == 0 or max_blocks == 0:
        return torch.full_like(pos, -1)
    phys = tables[torch.where(valid, req, 0), torch.where(valid, logical, 0)]
    valid &= (phys >= 0) & (phys < num_physical_blocks)
    slots = phys * block_size + torch.remainder(pos, block_size)
    return torch.where(valid, slots, torch.full_like(slots, -1))


def reference_paged_kv_gather(kv_cache, slots):
    import torch

    num_blocks, block_size = kv_cache.shape[:2]
    rows = kv_cache.reshape(num_blocks * block_size, -1)
    valid = (slots >= 0) & (slots < rows.shape[0])
    out = torch.zeros((slots.shape[0], rows.shape[1]), dtype=kv_cache.dtype)
    out[valid] = rows[slots[valid]]
    return out.reshape((slots.shape[0], *kv_cache.shape[2:]))


# ---------------------------------------------------------------------------
# Random allocator states
# ---------------------------------------------------------------------------

@dataclass
class PagedCase:
    block_tables: np.ndarray  # int32 [num_reqs, max_blocks], -1 = unallocated
    req_ids: np.ndarray       # int32 [n]
    token_pos: np.ndarray     # int32 [n]
    num_physical_blocks: int
    allocated: np.ndarray     # int32 [num_reqs], logical blocks owned per request


def make_paged_case(
    seed: int,
    *,
    num_reqs: int = 8,
    max_blocks: int = 12,
    num_physical_blocks: int = 64,
    n_queries: int = 2048,
    out_of_range_fraction: float = 0.15,
) -> PagedCase:
    """Disjoint ownership (one shuffled free list) plus deliberately invalid queries."""
    rng = np.random.default_rng(seed)
    tables = np.full((num_reqs, max_blocks), -1, dtype=np.int32)
    free = rng.permutation(num_physical_blocks).astype(np.int32)
    allocated = np.zeros(num_reqs, dtype=np.int32)
    cursor = 0
    for r in range(num_reqs):
        want = int(rng.integers(0, max_blocks + 1))
        take = min(want, num_physical_blocks - cursor)
        tables[r, :take] = free[cursor:cursor + take]
        allocated[r] = take
        cursor += take

    req = rng.integers(0, max(num_reqs, 1), size=n_queries, dtype=np.int32)
    pos = np.empty(n_queries, dtype=np.int32)
    for i in range(n_queries):
        owned = int(allocated[req[i]]) * BLOCK_SIZE if num_reqs else 0
        pos[i] = rng.integers(0, owned) if owned else 0
    bad = rng.random(n_queries) < out_of_range_fraction
    kinds = rng.integers(0, 4, size=n_queries)
    req[bad & (kinds == 0)] = -1
    req[bad & (kinds == 1)] = num_reqs
    pos[bad & (kinds == 2)] = -1 - rng.integers(0, 5, size=int(np.sum(bad & (kinds == 2))), dtype=np.int32)
    pos[bad & (kinds == 3)] = max_blocks * BLOCK_SIZE + rng.integers(0, 40, size=int(np.sum(bad & (kinds == 3))), dtype=np.int32)
    return PagedCase(tables, req, pos, num_physical_blocks, allocated)


def random_kv_cache(seed: int, num_physical_blocks: int, num_kv_heads: int = 2, head_dim: int = 128) -> np.ndarray:
    """float32 [num_blocks, 16, num_kv_heads, head_dim]; defaults match Muse Glimmer 30B's KV heads."""
    rng = np.random.default_rng(seed + 10_000)
    return rng.standard_normal((num_physical_blocks, BLOCK_SIZE, num_kv_heads, head_dim), dtype=np.float32)


def main(argv: Sequence[str] | None = None) -> int:
    import pytest

    args = list(argv if argv is not None else sys.argv[1:])
    return int(pytest.main([str(REPO_ROOT / "tests" / "test_differential.py"), "-v", *args]))


if __name__ == "__main__":
    sys.exit(main())
