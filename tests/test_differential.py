"""Runtime (CUDA or CPU_FALLBACK build) vs. PyTorch references on identical random inputs."""

import numpy as np
import pytest

torch = pytest.importorskip("torch")

from src.telemetry.differential_tester import (  # noqa: E402
    BLOCK_SIZE,
    GlimmerRuntime,
    GlimmerRuntimeError,
    make_paged_case,
    random_kv_cache,
    reference_paged_kv_gather,
    reference_paged_kv_index,
)


@pytest.fixture(scope="module")
def runtime() -> GlimmerRuntime:
    try:
        return GlimmerRuntime()
    except FileNotFoundError as exc:
        pytest.skip(str(exc))


def _reference(case) -> torch.Tensor:
    return reference_paged_kv_index(
        torch.from_numpy(case.block_tables), torch.from_numpy(case.req_ids), torch.from_numpy(case.token_pos),
        case.num_physical_blocks,
    )


@pytest.mark.parametrize("zero_copy", [False, True], ids=["staged", "zero_copy"])
@pytest.mark.parametrize("seed", range(12))
def test_index_matches_reference(runtime, seed, zero_copy):
    case = make_paged_case(seed)
    ours = torch.from_numpy(
        runtime.paged_kv_index(case.block_tables, case.req_ids, case.token_pos, case.num_physical_blocks,
                               zero_copy=zero_copy)
    )
    ref = _reference(case)
    assert torch.equal(ours, ref), f"{int((ours != ref).sum())} mismatching slots"
    masked = int((ref == -1).sum())
    assert 0 < masked < ref.numel(), "case should exercise both predicated-off and valid lanes"


@pytest.mark.parametrize("seed", range(6))
def test_gather_matches_reference(runtime, seed):
    case = make_paged_case(seed, n_queries=513)
    cache = random_kv_cache(seed, case.num_physical_blocks)
    slots = runtime.paged_kv_index(case.block_tables, case.req_ids, case.token_pos, case.num_physical_blocks)
    ours = torch.from_numpy(runtime.paged_kv_gather(cache, slots))
    ref = reference_paged_kv_gather(torch.from_numpy(cache), torch.from_numpy(slots))
    assert ours.shape == ref.shape == (513, 2, 128)
    assert torch.allclose(ours, ref, atol=1e-3, rtol=0)


@pytest.mark.parametrize("seed", range(6))
def test_isolation_witness(runtime, seed):
    """Runtime counterpart of `paged_kv_isolation`: distinct requests never share a slot."""
    case = make_paged_case(seed, n_queries=4096, out_of_range_fraction=0.0)
    slots = runtime.paged_kv_index(case.block_tables, case.req_ids, case.token_pos, case.num_physical_blocks)
    owners: dict[int, int] = {}
    for req, slot in zip(case.req_ids.tolist(), slots.tolist()):
        if slot >= 0:
            assert owners.setdefault(slot, req) == req, f"slot {slot} shared by requests {owners[slot]} and {req}"
    assert np.all(slots[slots >= 0] < case.num_physical_blocks * BLOCK_SIZE)


def test_edge_shapes(runtime):
    empty = runtime.paged_kv_index(np.zeros((3, 4), np.int32), np.array([], np.int32), np.array([], np.int32), 8)
    assert empty.shape == (0,)
    no_table = runtime.paged_kv_index(np.zeros((0, 0), np.int32), np.array([0, 1], np.int32), np.array([0, 5], np.int32), 8)
    assert no_table.tolist() == [-1, -1]
    table = np.array([[3, -1, 7]], np.int32)
    got = runtime.paged_kv_index(table, np.array([0, 0, 0, 0], np.int32), np.array([0, 17, 33, 47], np.int32), 8)
    assert got.tolist() == [3 * 16 + 0, -1, 7 * 16 + 1, 7 * 16 + 15]
    out_of_pool = runtime.paged_kv_index(table, np.array([0], np.int32), np.array([32], np.int32), 7)
    assert out_of_pool.tolist() == [-1]


def test_invalid_arguments_raise(runtime):
    with pytest.raises(GlimmerRuntimeError, match="non-negative"):
        runtime.paged_kv_index(np.zeros((1, 1), np.int32), np.array([0], np.int32), np.array([0], np.int32), -1)


def test_no_leaks(runtime):
    case = make_paged_case(0)
    for zero_copy in (False, True):
        runtime.paged_kv_index(case.block_tables, case.req_ids, case.token_pos, case.num_physical_blocks,
                               zero_copy=zero_copy)
    runtime.paged_kv_gather(random_kv_cache(0, case.num_physical_blocks), np.arange(10, dtype=np.int64))
    assert runtime.live_device_bytes() == 0
    assert runtime.live_pinned_bytes() == 0
