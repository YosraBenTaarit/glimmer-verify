# glimmer-verify

**Prefix-Cached Agentic Autoformalization, Runtime FFI Glue, and Differential Telemetry of LLM Inference Components using Muse Glimmer 30B**

`glimmer-verify` is a research artifact with four parts:

1. **Runtime.** A small C++17/CUDA runtime for a paged KV-cache indexer, with RAII ownership of device and pinned host memory, a C ABI, and a zero-copy OCaml `Bigarray` FFI stub.
2. **Lean 4 proofs.** Machine-checked theorems about that runtime: predicated-lane memory safety and cross-tenant KV-cache isolation.
3. **Proof-repair agent.** A loop in which `meta-models/Muse-Glimmer-30B` writes Lean 4 proofs for kernel safety specifications and repairs them from compiler feedback. The conversation prefix is kept byte-stable across turns so vLLM Automatic Prefix Caching and SGLang RadixAttention can reuse it.
4. **Measurement.** A differential-testing and telemetry suite. It checks the runtime against PyTorch references and records the serving-side cost of the repair loop: TTFT, ITL/TPOT, prefix-cache hit rate, iterations to convergence, KV-cache pressure, and GPU utilization.

---

## Contents

- [Claims and scope](#claims-and-scope)
- [Repository layout](#repository-layout)
- [Hardware tiers](#hardware-tiers)
- [Getting started (≈20 min, no GPU)](#getting-started-20-min-no-gpu)
- [Experiments](#experiments)
- [Configuration reference](#configuration-reference)
- [Trusted computing base and threats to validity](#trusted-computing-base-and-threats-to-validity)
- [Model notes: Muse Glimmer 30B](#model-notes-muse-glimmer-30b)

---

## Claims and scope

| ID | Claim | Evidence | Experiment |
|----|-------|----------|------------|
| C1 | Predicated lanes of the indexer never access outside `[base, base + 4n)` | `ptx_predicate_bounds_safe` (Lean, no `sorry`) | E2 |
| C2 | Requests with disjoint allocated page-table entries never share a physical KV slot | `paged_kv_isolation` (Lean, no `sorry`) | E2 |
| C3 | The CUDA/C++ runtime matches the PyTorch reference bit-exactly for slot indices and within `atol=1e-3` for gathered KV rows | `tests/test_differential.py` | E1 |
| C4 | `DeviceTensor` / `PinnedHostBuffer` release every byte they allocate, including on exception paths | `glimmer_harness` live-byte accounting | E1 |
| C5 | The repair loop's prompts are append-only, so turn *k+1*'s prompt has turn *k*'s full prompt and response as a byte prefix | `tests/test_agent_loop.py::test_prefix_is_append_only` | E3 |
| C6 | We measure, and do not assume, the resulting prefix-cache hit rate, TTFT, and iterations to convergence | `runs/*/turns.csv`, `plots/` | E3, E4 |

What is **not** claimed:

- The Lean models are written over `Nat`. Their correspondence with the C++ source is established by inspection plus differential testing, not by a verified compiler. Benchmark task B01 asks for the 64-bit no-wrap refinement.
- In *autoformalize* mode, the agent writes theorem statements itself. Lean guarantees that a proof is valid for the statement written, not that the statement captures the intended specification. Those statements are saved for human review (see [threats to validity](#trusted-computing-base-and-threats-to-validity)).
- NVML utilization counters are time fractions ("was the SM / memory controller busy during the sample window"), not achieved FLOP/s or GB/s. The "roofline" plot is labelled accordingly.

## Repository layout

```text
glimmer-verify/
├── README.md
├── .env.example                      # BACKEND=openrouter | local_server, model ids, telemetry switches
├── .gitattributes                    # LF for *.sh / *.lean / Makefile (Windows checkouts)
├── pyproject.toml                    # Python package `glimmer_verify` (maps to src/)
├── CMakeLists.txt                    # -DCPU_FALLBACK=ON builds without the CUDA toolkit
├── Makefile                          # runtime / harness / ptx / lean / test / agent / plots
├── src/
│   ├── runtime/                      # Module 1: C++17 RAII + CUDA + FFI glue
│   │   ├── cuda_compat.hpp           #   CUDA runtime vs. host-only CPU_FALLBACK switch
│   │   ├── tensor_raii.hpp           #   DeviceTensor, PinnedHostBuffer, HostRegistration, CudaStream
│   │   ├── paged_kv_indexer.cuh      #   launcher declarations, 16-token block constants
│   │   ├── paged_kv_indexer.cu       #   predicated + coalesced indexer kernel, KV gather kernel (PTX target)
│   │   ├── cuda_glue.cu              #   C ABI: staged (pinned→device) and zero-copy (mapped) paths
│   │   ├── glimmer_runtime.h         #   public C header (ctypes, OCaml, harness)
│   │   ├── cpu_fallback_unity.cpp    #   compiles the .cu sources as plain C++17
│   │   ├── harness_main.cpp          #   C++ harness: reference check, isolation witness, leak accounting
│   │   └── ocaml_c_ffi_stub.c        #   Bigarray → CUDA with the OCaml runtime lock released
│   ├── verification/GlimmerVerify/   # Module 2: Lean 4 project
│   │   ├── lakefile.lean
│   │   ├── lean-toolchain
│   │   ├── GlimmerVerify.lean
│   │   └── GlimmerVerify/PagedKVProofs.lean
│   ├── agent/                        # Module 3: Muse Glimmer 30B proof-repair loop
│   │   ├── glimmer_client.py         #   dual backend (OpenRouter / vLLM / SGLang), streaming timings
│   │   ├── lean_checker.py           #   `lake env lean`, diagnostics, axiom audit, template integrity
│   │   ├── prompts.py                #   byte-stable system prompt, task prompt, compiler feedback
│   │   └── proof_repair_agent.py     #   multi-turn repair loop + CLI
│   └── telemetry/                    # Module 4
│       ├── differential_tester.py    #   ctypes runtime binding, PyTorch references, pytest entry point
│       └── metrics_collector.py      #   TTFT/ITL/hit-rate, Prometheus scrape, NVML sampler, CSV, plots
├── benchmarks/
│   ├── sources/                      #   kernel/PTX excerpts referenced by tasks
│   ├── unproven_theorems/            #   `sorry` templates + manifest.json (agent tasks)
│   └── reference_solutions/          #   human proofs proving every task is solvable (never shown to the agent)
├── tests/                            # pytest: differential, Lean checker, template integrity, agent loop, telemetry
├── docker/
│   ├── docker-compose.yml            # profiles `vllm` | `sglang`, plus Prometheus + Grafana
│   ├── prometheus/prometheus.yml     # scrapes the compose engines and host.docker.internal
│   └── grafana/
│       ├── provisioning/             #   datasource + dashboard provider
│       └── dashboards/               #   "glimmer-verify inference" dashboard JSON
├── scripts/
│   ├── launch_vllm.sh                # compose (default) | --native | --down
│   └── launch_sglang.sh
├── experiments/
│   ├── README.md                     # OpenRouter today → vLLM/SGLang Meta stack later
│   └── protocols/                    # frozen factorial designs (memory × seed)
├── results/                          # checked-in evaluation tables and raw run data
├── runs/                             # (generated) per-run CSV/JSON telemetry and transcripts
└── plots/                            # (generated) ttft_vs_retry_turn.png, roofline_bandwidth_vs_compute.png, ...
```

## Hardware tiers

| Tier | Hardware | What runs |
|------|----------|-----------|
| T0 | Any x86-64/ARM laptop, no GPU | `CPU_FALLBACK` runtime + harness, differential tests, Lean proofs, agent via `BACKEND=openrouter` |
| T1 | Any machine with the CUDA toolkit (GPU optional) | everything in T0, plus `make ptx` (`nvcc -ptx` does not need a GPU) |
| T2 | NVIDIA GPU, compute capability ≥ 6.0 | CUDA runtime build, zero-copy path, NVML sampling |
| T3 | 24 GB GPU (L4 / A10G / RTX 4090) | self-hosted model with a **4-bit** checkpoint (see [model notes](#model-notes-muse-glimmer-30b)) |
| T4 | 80 GB GPU (A100 / H100) | self-hosted BF16 model, full prefix-caching telemetry |

## Getting started (≈20 min, no GPU)

Prerequisites: Python ≥ 3.10, a C++17 compiler, CMake ≥ 3.20 or GNU make, and [`elan`](https://github.com/leanprover/elan) for Lean 4.

```bash
# 1. Python environment
python -m venv .venv && source .venv/bin/activate        # Windows: .venv\Scripts\activate
pip install -e ".[dev,diff]"                             # add ",gpu" for pynvml on GPU hosts

# 2. Runtime without CUDA (T0)
cmake -S . -B build -DCPU_FALLBACK=ON && cmake --build build -j
ctest --test-dir build --output-on-failure               # or: make test-runtime CPU_FALLBACK=1

# 3. Lean library (downloads the pinned toolchain on first run)
cd src/verification/GlimmerVerify && lake build && cd -

# 4. All Python tests (differential + Lean checker + agent loop)
pytest -q

# 5. Agent against OpenRouter
cp .env.example .env            # set OPENROUTER_API_KEY
python -m src.agent.proof_repair_agent --tasks B03_physslot_in_bounds --print-prompt   # inspect prompts, no API call
python -m src.agent.proof_repair_agent --tasks B03_physslot_in_bounds
```

If `pytest` hangs at startup with no output, a globally installed plugin is usually responsible (this happens with some Anaconda base environments). Run `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q`, or use a clean venv.

Expected: the harness prints `all checks passed`, `lake build` finishes with no `sorry` warnings, `pytest` is green (tests that need an unavailable tool are *skipped* with a reason, never silently passed), and the agent writes `runs/<run-id>/`.

## Experiments

### E1: Runtime correctness and memory hygiene (C3, C4)

```bash
make runtime harness CPU_FALLBACK=1   # or CUDA: make runtime harness CUDA_ARCH=sm_80
make test-runtime
pytest tests/test_differential.py -v  # torch.equal for slots, torch.allclose(atol=1e-3) for KV rows
make ptx CUDA_ARCH=sm_80              # -> build/ptx/paged_kv_indexer.ptx (needs nvcc, not a GPU)
```

The differential tests build random allocator states with disjoint block ownership and unallocated `-1` entries, and add queries that are deliberately out of range (negative positions, unknown requests, positions past the last allocated block). The same inputs go to the PyTorch reference, which uses the `slot_mapping` formula of vLLM's `reshape_and_cache`, and to both runtime paths: staged pinned→device copies, and zero-copy mapped host memory.

### E2: Lean proofs (C1, C2)

```bash
make lean          # lake build; fails on any error
make lean-bench    # checks every reference solution against its template with the agent's own checker
```

`GlimmerVerify/PagedKVProofs.lean` contains `ptx_predicate_bounds_safe` and `paged_kv_isolation`, each closed with `unfold` / `split` / `omega`. `#print axioms` reports only Lean's standard axioms.

### E3: Agentic proof repair with prefix caching (C5, C6)

```bash
# Laptop: OpenRouter (same agent as the Meta stack; only the serving URL changes)
BACKEND=openrouter python -m src.agent.proof_repair_agent --max-retries 8 --memory append

# Factorial: memory strategy × seed. Protocols live in experiments/protocols/.
python -m src.experiments.matrix experiments/protocols/openrouter_scale.json --dry-run

# Cloud GPU: official weights on vLLM with Automatic Prefix Caching
bash scripts/launch_vllm.sh         # or: bash scripts/launch_sglang.sh; --native skips docker for the engine
BACKEND=local_server LOCAL_SERVER_KIND=vllm \
  python -m src.experiments.matrix experiments/protocols/vllm_meta_stack.json
```

See [experiments/README.md](experiments/README.md) for the OpenRouter → vLLM/SGLang path and the three memory strategies (`append`, `last_error`, `drop_truncated`).

Each task starts as one conversation:

```text
[system: fixed contract + trusted library source]  ← identical across all tasks  (stable prefix)
[user:   task spec + source + template]            ← identical across retries of a task
[assistant: attempt 1] [user: Lean diagnostics 1]
[assistant: attempt 2] [user: Lean diagnostics 2] ...  up to 1 + MAX_RETRIES attempts
```

In `append` mode messages are only ever appended, so turn *k+1* re-sends turn *k* as an exact prefix. `last_error` keeps the two-message prefix and replaces the failed suffix with the latest Lean diagnostic. Prompts contain no timestamps, absolute paths, or random IDs. The candidate is checked by `lake env lean` in three ways:

1. **Template integrity.** Only the `sorry` holes may change, and the checked file is rebuilt from the template.
2. **Diagnostics.** No errors and no `sorry` warnings.
3. **Axiom audit.** `#print axioms` must list only `propext`, `Classical.choice`, and `Quot.sound`.

Per-turn telemetry goes to `runs/<run-id>/turns.csv`, and transcripts go to `runs/<run-id>/tasks/<task>/`.

### E4: Telemetry and plots

```bash
python -m src.telemetry.metrics_collector plot --run-dir runs/<run-id> --out plots/
```

| Output | Content |
|--------|---------|
| `plots/ttft_vs_retry_turn.png` | median TTFT (IQR band) per retry turn, overlaid with the prefix-cache hit rate |
| `plots/roofline_bandwidth_vs_compute.png` | NVML memory-controller busy % vs. SM busy %, coloured by phase (generation / Lean check / idle) |
| `plots/iterations_to_convergence.png` | histogram of attempts-to-proof, plus unconverged tasks |

There are two sources of prefix-cache hit rate. The **client** rate is `usage.prompt_tokens_details.cached_tokens / prompt_tokens`; it needs vLLM `--enable-prompt-tokens-details` or SGLang `--enable-cache-report`, and OpenRouter reports it for providers that cache. The **server** rate comes from deltas of the Prometheus prefix-cache counters scraped around each request. Server-side KV usage (`vllm:kv_cache_usage_perc` / `vllm:gpu_cache_usage_perc` / `sglang:token_usage`) and preemptions are recorded per turn. Grafana at `http://localhost:3000` shows the same series live.

## Configuration reference

All settings are read from the environment or `.env` (see `.env.example`).

| Variable | Default | Meaning |
|----------|---------|---------|
| `BACKEND` | `openrouter` | `openrouter` or `local_server` |
| `OPENROUTER_MODEL` | `meta/muse-glimmer-30b` | OpenRouter model slug |
| `LOCAL_SERVER_KIND` | `vllm` | `vllm` (`:8000/v1`) or `sglang` (`:30000/v1`) |
| `LOCAL_MODEL` | `meta-models/Muse-Glimmer-30B` | must equal the server's `--served-model-name` |
| `MAX_RETRIES` | `8` | repair turns after the first attempt |
| `GLIMMER_NVML` | `auto` | `auto` samples the local GPU only when `BACKEND=local_server` |
| `LAKE_CMD` | `lake` | path to `lake` if not on `PATH` |

## Trusted computing base and threats to validity

- **Trusted:** the Lean 4 kernel, the pinned toolchain, `GlimmerVerify/PagedKVProofs.lean` definitions, and the benchmark templates' statements. The agent cannot edit any of them in *complete* mode, because the checked file is rebuilt from the template with only the proof holes replaced.
- **Rejected tokens in proofs:** `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `set_option`, `run_tac`/`run_cmd`/`run_elab`, and notation/macro commands. The `#print axioms` audit is the semantic backstop if a lexical rule is ever bypassed.
- **Statement fidelity (autoformalize mode):** the generated statements are written to `runs/<id>/tasks/<task>/final.lean` and must be reviewed by a human before being counted as verification of the kernel.
- **CPU_FALLBACK semantics:** CUDA threads execute sequentially on the host. This is sound for the kernels in this repo, which use no `__syncthreads`, shared memory, or warp intrinsics, but it says nothing about data races on real hardware.
- **Prefix-cache measurements:** a hit requires the server's chat template to re-render previous assistant turns exactly as generated. Templates that strip reasoning from history reduce the hit rate after the first assistant turn. Report the observed rate from `turns.csv`, not a target.

## Model notes: Muse Glimmer 30B

From the published `config.json` of `meta-models/Muse-Glimmer-30B` (architecture `MuseGlimmerForConditionalGeneration`, `image-text-to-text`, Apache-2.0):

- Text tower: 52 layers, hidden 6656, 32 query heads, **2 KV heads**, head dim 128, 131 072-token context.
- Attention is hybrid: 3 of every 4 layers use a **2048-token sliding window**, and every 4th layer uses full attention.
- KV cost: full-attention layers store 2 × 2 × 128 × 2 B = 1 KiB per token per layer. That is ≈13 KiB/token over the 13 full-attention layers, plus at most 2048 tokens' worth in each sliding layer. Long repair conversations are therefore cheap to keep cached.
- Weights are published in BF16 only (≈60 GB). On a 24 GB GPU, use a 4-bit (AWQ/GPTQ) community checkpoint via `MODEL_ID=...` and `QUANTIZATION=awq|gptq`. FP8 (≈30 GB) does not fit.
- Serving `muse_glimmer` requires a vLLM/SGLang build that knows the architecture. If your build does not, `VLLM_EXTRA_ARGS="--model-impl transformers"` uses the Transformers backend. For text-only use, `--limit-mm-per-prompt '{"image":0,"video":0}'` avoids reserving vision-encoder memory.
