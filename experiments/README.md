# Experiment protocols

The agent, Lean checker and prompts do not change between OpenRouter and a
self-hosted vLLM/SGLang stack. What changes is **who serves Muse Glimmer 30B**.

| Stage | Where the model runs | What you measure | Hardware |
|---|---|---|---|
| Now | OpenRouter → DeepInfra BF16 (`meta/muse-glimmer-30b`) | Proof rate, repair, client cache hits, cost | Laptop + API credit |
| Next | vLLM or SGLang, official weights `meta-models/Muse-Glimmer-30B` | Same metrics **plus** Prometheus prefix-cache counters, KV usage, preemptions, NVML | T3 24 GB (4-bit) or T4 80 GB (BF16) |
| Meta stack | Same engine flags Meta publishes for APC / RadixAttention | Server-side hit rate vs. client `cached_tokens`; compare `append` vs `last_error` | Cluster |

## Memory strategies

Every strategy keeps `[system, task]` byte-identical (the cacheable prefix).

- `append` — full history. Highest prefix reuse; also the path that produced empty 4-token replies after repeated truncation.
- `last_error` — only the latest failed attempt + Lean diagnostics. Tests whether a short contrastive error is enough to repair, at the cost of not caching failed turns.
- `drop_truncated` — append-only except empty assistant turns are omitted. The intervention suggested by the collapse replay.

## Commands

```bash
# Print the 3×3 OpenRouter matrix without calling the API
python -m src.experiments.matrix experiments/protocols/openrouter_scale.json --dry-run

# One cell (example): last_error, seed 1, 12-task suite
python -m src.agent.proof_repair_agent --memory last_error --run-dir runs/probe_last_error

# Full OpenRouter matrix (9 runs). Budget: ~$1 at the 8k/6k setting.
python -m src.experiments.matrix experiments/protocols/openrouter_scale.json --out runs/openrouter_scale_v1

# After a T4 box is up:
bash scripts/launch_vllm.sh
BACKEND=local_server LOCAL_SERVER_KIND=vllm \
  python -m src.experiments.matrix experiments/protocols/vllm_meta_stack.json --out runs/vllm_meta_stack_v1

python -m src.telemetry.compare_runs runs/openrouter_scale_v1
```

vLLM must be started with `--enable-prefix-caching --enable-prompt-tokens-details`.
SGLang must be started with `--enable-metrics --enable-cache-report`. Those flags
are already in `scripts/launch_vllm.sh` / `scripts/launch_sglang.sh`.
