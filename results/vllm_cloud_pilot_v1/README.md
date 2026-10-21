# vLLM A100 cloud pilot (21 Oct 2026) — aborted after B01

This is a **real run on official weights**, not a failed setup. It is **not** a
10-task confirmation of the OpenRouter table. Do not quote it as “vLLM proved
5/10” or “the Meta stack matches OpenRouter.”

OpenRouter remains the proof-rate result (`results/2026-10-20_muse-glimmer-30b/`,
n=3). This folder is the first engine-side trace: vLLM Automatic Prefix Caching
on `meta-models/Muse-Glimmer-30B`, A100 80GB.

## Setup

| | |
|---|---|
| GPU | RunPod Secure A100 80GB PCIe (`b7866e24346c`), then **terminated** |
| Engine | vLLM `serve` with `--enable-prefix-caching --enable-prompt-tokens-details --max-model-len 8192` |
| Weights | Hugging Face `meta-models/Muse-Glimmer-30B` (BF16, ~73 GiB resident of 80 GiB) |
| Protocol | `experiments/protocols/vllm_cloud_pilot.json` (append vs last_error, seed 1, tasks B01–B08 + A01–A02) |
| Harness | laptop clone of this repo; `scripts/cloud_vllm_pilot.sh` |

## What finished

| Cell | Tasks completed | B01 | B02 | Crash |
|---|---|---|---|---|
| `memory=append_seed=1` | B01 written to `tasks.csv`; B02 attempt 1 ran | proved in 2 tries | `lean_error`, `finish_reason=length` (5662 completion tokens) | B02 attempt 2: HTTP 400, prompt ≥ 8193 vs cap 8192 |
| `memory=last_error_seed=1` | B01 written; B02 attempt 1 ran | proved first try | `no_code` truncated at length | same 400 on the next turn |

The agent does not catch that 400, so the cell dies and the remaining eight
tasks never start. `returncode` in each `experiment.json` is 1 for that reason.

## Numbers you can cite from this folder

From `turns.csv` / per-cell `summary.json` / `gpu_samples.csv` / `server_samples.csv`:

| Measurement | append | last_error |
|---|---|---|
| B01 | proved, turn 1 TTFT 6.43s (0/2555 cached) → turn 2 TTFT 0.60s (2544/4630 cached, 55%) | proved first try, TTFT 0.10s (2544/2555 cached) |
| Server prefix-cache hit rate (Prometheus) | matches the client `cached_tokens` column | same |
| Preemptions | 0 | 0 |
| GPU | ~72748 MiB / 81920 MiB while idle after load; SM util hits 100% while generating | same machine |
| API cost | $0 (self-hosted) | $0 |

**Caveat on last_error B01:** both cells used the **same live vLLM process**. The
~100% turn-1 cache hit on last_error B01 is the previous cell’s B01 prefix still
in GPU KV, not an independent cold start. That is still evidence that APC works;
it is not a fair between-cell comparison.

Aggregated markdown (1 completed task per cell): `table.md`. Regenerated with:

```bash
python -m src.telemetry.compare_runs results/vllm_cloud_pilot_v1 --json results/vllm_cloud_pilot_v1/summary.json
```

## Why 8192 broke the 10-task matrix

`--max-model-len 8192` was chosen to match the OpenRouter 8k protocol. After a
long truncated B02 attempt, the **next** repair prompt was 8193 input tokens.
vLLM rejects that before any decode. OpenRouter can still be an 8k *output*
budget; this engine cap is on **prompt + output** together.

A rerun that finishes 10 tasks is a **new protocol**, not a repeat of this one:

1. Raise `--max-model-len` (16384 or 32768 on an 80 GB card).
2. Catch HTTP 400 / context overflow in the agent and continue the cell.
3. Cold-start vLLM (or flush the cache) between cells if you want independent
   turn-1 hit rates.
4. Keep this folder as the 8k-cap abort. Do not overwrite it.

Until that rerun exists, the honest public sentence is: *official 30B served on
vLLM/A100 with APC counters; the 8k context cap aborted both cells on B02.*
