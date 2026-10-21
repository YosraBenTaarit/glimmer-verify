# glimmer-verify

**Experimental research artifact** for *prefix-cached agentic autoformalization* of a real LLM inference component: a paged KV-cache indexer, checked in Lean 4, repaired by [Muse Glimmer 30B](https://huggingface.co/meta-models/Muse-Glimmer-30B), and measured on vLLM / SGLang.

**Keywords:** Lean 4, autoformalization, proof repair, paged KV cache, prefix caching, Automatic Prefix Caching, RadixAttention, vLLM, SGLang, Muse Glimmer, ML systems, CUDA, RAII, differential testing.

> This is **not** a production library, **not** a complete verification of vLLM, and **not** an official Meta or EPFL release. It is a small, repeatable experiment: freeze the protocol, measure what the serving stack actually does, and do not claim more than the traces support.

---

## Status (pilot)

| | |
|---|---|
| Object | 16-token paged KV indexer (C++17/CUDA) + Lean 4 models of bounds and isolation |
| Agent | Muse Glimmer 30B writes/repairs Lean proofs from compiler diagnostics |
| OpenRouter (n=3 seeds) | ~5/10 tasks proved; prefix-cache and cost logged; empty-reply collapse reproduced |
| vLLM on official weights | A100 80GB served BF16 30B with APC; both cells aborted on B02 at the 8192 context cap ([`results/vllm_cloud_pilot_v1/`](results/vllm_cloud_pilot_v1/)) |
| Scale | 12 benchmark tasks, 3 memory strategies, not a large-N paper yet |

Raw tables: [`results/2026-10-20_muse-glimmer-30b/`](results/2026-10-20_muse-glimmer-30b/). Protocols: [`experiments/`](experiments/).

---

## Why this exists (Keystone-style stance)

The experiment is built in the spirit of **hardware–software co-design and small trusted bases** (the Keystone philosophy): you do not “trust the model,” you **measure the system you actually run**.

1. **The object is a real inference part**, not a toy arithmetic quiz. Paged KV indexing is where vLLM-style engines map `(request, token)` to physical cache blocks. Isolation failures here are cross-tenant bugs.
2. **Lean is the teacher, not the model.** A proof counts only if `lake env lean` accepts it, the template statement is untouched, and `#print axioms` lists only Lean’s standard axioms.
3. **The conversation is part of the system.** Repair is multi-turn. If the prefix is byte-stable, vLLM Automatic Prefix Caching / SGLang RadixAttention can reuse KV blocks. If you rewrite history, you trade cache hits for a cleaner error. That trade-off is the measurement, not a slogan.
4. **Overclaiming is a bug.** Lean models are over `Nat`; correspondence to C++ is by inspection plus tests, not a verified compiler. Autoformalized *statements* still need a human. API proxies (OpenRouter) measure the model; engine counters need vLLM on official weights.

---

## What is in the repo

| Part | What it is |
|------|------------|
| **Runtime** | RAII `DeviceTensor` / pinned host buffers, predicated indexer kernel, gather kernel, C ABI, optional OCaml Bigarray stub, `CPU_FALLBACK` without a GPU |
| **Lean 4** | Closed theorems `ptx_predicate_bounds_safe` and `paged_kv_isolation`; 12 agent tasks (B01–B10 complete, A01–A02 autoformalize) with human reference proofs the agent never sees |
| **Agent** | Dual backend: OpenRouter *or* local vLLM/SGLang. Memory views: `append`, `last_error`, `drop_truncated` |
| **Telemetry** | Differential tests vs PyTorch (`atol=1e-3`), TTFT / ITL / prefix-cache hit rate, Prometheus, NVML, CSV + plots |

Same agent, same prompts, same Lean checker on a laptop (OpenRouter) and on an A100 (vLLM). Only the server changes.

---

## Claims (and what we do not claim)

| ID | Claim | Evidence |
|----|--------|----------|
| C1 | Predicated indexer lanes stay inside `[base, base + 4n)` | Lean `ptx_predicate_bounds_safe` |
| C2 | Disjoint page tables never share a physical KV slot | Lean `paged_kv_isolation` |
| C3 | Runtime matches a PyTorch/vLLM-style reference for slots and gathered rows | `tests/test_differential.py` |
| C4 | RAII handles free device/pinned bytes, including on errors | `glimmer_harness` |
| C5 | `append` mode is prefix-stable across turns | `test_prefix_is_append_only` |
| C6 | Cache hit rate, TTFT, and iterations are *measured* | `turns.csv`, `results/` |

**Not claimed:** bit-precise 64-bit wrapping (task B01); that autoformalized statements match the kernel (human review); that NVML `%` is FLOP/s; that OpenRouter is vLLM; that 5/10 on n=3 is a leaderboard score.

---

## Quick start (laptop, no GPU, ~20 min)

Python ≥ 3.10, a C++17 compiler, CMake ≥ 3.20, [`elan`](https://github.com/leanprover/elan).

```bash
python -m venv .venv && source .venv/bin/activate    # Windows: .venv\Scripts\activate
pip install -e ".[dev,diff]"

cmake -S . -B build -DCPU_FALLBACK=ON && cmake --build build -j
ctest --test-dir build --output-on-failure

cd src/verification/GlimmerVerify && lake build && cd -
pytest -q

cp .env.example .env    # set OPENROUTER_API_KEY if you call a model
python -m src.agent.proof_repair_agent --tasks B03 --print-prompt
```

If `pytest` hangs with no output: `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q`.

**vLLM on an 80 GB GPU** (official weights, prefix caching): [experiments/CLOUD.md](experiments/CLOUD.md).  
**Hardware tiers T0–T4, env vars, threats to validity:** below.

---

## Experiments

| | Command |
|--|---------|
| Runtime + differential tests | `make test-runtime` then `pytest tests/test_differential.py` |
| Lean library + reference proofs | `make lean` and `make lean-bench` |
| One proof-repair task | `python -m src.agent.proof_repair_agent --tasks B03 --memory append` |
| OpenRouter factorial (dry run) | `python -m src.experiments.matrix experiments/protocols/openrouter_scale.json --dry-run` |
| Inspect a finished run | `python -m src.agent.proof_repair_agent --inspect results/2026-10-20_muse-glimmer-30b/frozen_d8874c4/max4k_s1 --failed-only` |
| Plots | `python -m src.telemetry.metrics_collector plot --run-dir runs/<id> --out plots/` |

Memory strategies (stable `[system, task]` prefix in all cases):

- `append` — full history (max cache reuse; can collapse after many truncated turns)
- `last_error` — only the latest Lean diagnostic (cleaner repair, less cache after turn 1)
- `drop_truncated` — drop empty assistant turns

Acceptance: template integrity, no `sorry`/`admit`/…, Lean errors none, axiom audit.

---

## Hardware tiers

| Tier | Hardware | What runs |
|------|----------|-----------|
| T0 | Laptop, no GPU | CPU fallback runtime, Lean, agent via OpenRouter |
| T1 | CUDA toolkit (GPU optional) | `make ptx` |
| T2 | NVIDIA GPU, CC ≥ 6.0 | CUDA runtime, NVML |
| T3 | 24 GB | **4-bit** checkpoint only (not the BF16 Meta-stack match) |
| T4 | 80 GB (A100 / H100) | Official BF16 weights + vLLM APC |

---

## Repository layout

```text
src/runtime/                 C++17 RAII, CUDA kernels, C ABI, OCaml stub
src/verification/GlimmerVerify/   Lean 4 (toolchain pinned)
src/agent/                   OpenRouter / vLLM client, Lean checker, repair loop
src/telemetry/               differential tests, Prometheus/NVML, plots
src/experiments/             matrix runner, collapse replay
benchmarks/                  sorry templates, reference proofs, kernel excerpts
experiments/protocols/       frozen factorial JSON (OpenRouter, vLLM, cloud pilot)
results/                     checked-in pilot tables
docker/  scripts/            vLLM / SGLang + Prometheus + Grafana
```

---

## Configuration

See [`.env.example`](.env.example). Important variables: `BACKEND` (`openrouter` \| `local_server`), `OPENROUTER_MODEL=meta/muse-glimmer-30b`, `LOCAL_MODEL=meta-models/Muse-Glimmer-30B`, `AGENT_MEMORY`, `MAX_RETRIES`, `GLIMMER_MAX_TOKENS`, `GLIMMER_REASONING_MAX_TOKENS`.

---

## Trusted computing base

Trusted: Lean 4 kernel, pinned toolchain, library definitions, template *statements*.  
In complete mode the file Lean sees is **rebuilt from the template**; the model may only fill `sorry` holes.  
Rejected in proofs: `sorry`, `admit`, `native_decide`, new `axiom`s, `unsafe`, macros, `set_option`.  
CPU_FALLBACK runs threads serially (sound here: no `__syncthreads` / warp ops).  
Prefix-cache hits depend on the server’s chat template; report `turns.csv`, not a target.

---

## Muse Glimmer 30B (serving notes)

From the public `config.json` (`MuseGlimmerForConditionalGeneration`, Apache-2.0): 52 layers, 2 KV heads, hybrid attention (sliding window + full). BF16 weights ≈ 60 GB. Text-only serving: `--limit-mm-per-prompt '{"image":0,"video":0}'`. If vLLM lacks the architecture: `--model-impl transformers`.

---

## Citation

This artifact is unpublished. If you use it, cite the repository and the model:

```
Yosra Ben Taarit. glimmer-verify: experimental prefix-cached agentic autoformalization
of a paged KV indexer with Muse Glimmer 30B. https://github.com/YosraBenTaarit/glimmer-verify
```

Model: Meta, *Muse Glimmer 30B*, `meta-models/Muse-Glimmer-30B`.
