# Cloud vLLM pilot (A100 80GB, €20–30 budget)

This is **not** a full paper-scale eval. It is the smallest run that still uses
**official weights + vLLM Automatic Prefix Caching**, which OpenRouter cannot
give you. Two cells: `append` vs `last_error`, seed 1, the original 10 tasks.

I cannot rent the GPU for you. You pay RunPod (or Vast.ai) with your card,
SSH in, run one script, download the tarball, **delete the pod**.

## Cost (prices as of 21 Oct 2026)

| Item | Estimate |
|------|----------|
| GPU | 1× **A100 80GB** (BF16 30B needs ~60 GB; a 24 GB card is *not* the Meta stack) |
| RunPod Community | **$1.19 / hour** |
| RunPod Secure | **$1.79 / hour** |
| Vast.ai (cheapest listings) | ~**$0.50–0.70 / hour** (host quality varies) |
| Download + vLLM start | 20–40 min (once) |
| Two 10-task cells | typically **4–8 hours** |
| **Total at $1.19/hr** | about **€8–15** |
| **Leave yourself** | €5–10 spare so a slow cell does not empty the account |

€20–30 is enough for this pilot. It is **not** enough for 3 memories × 5 seeds
(that is ~40–50 GPU-hours).

Do **not** use 4-bit / a 24 GB GPU for this run. That is a different model
numerically, and you could no longer say “we matched the Meta stack.”

## What you do (RunPod, easiest)

1. Create an account at [runpod.io](https://www.runpod.io/pricing). Add €20–30.
2. Create a Hugging Face token at [huggingface.co/settings/tokens](https://huggingface.co/settings/tokens).
   Open [meta-models/Muse-Glimmer-30B](https://huggingface.co/meta-models/Muse-Glimmer-30B) and accept the licence if asked.
3. Deploy a **Pod**:
   - GPU: **A100 PCIe 80GB** (Community Cloud is fine)
   - Template: **RunPod PyTorch** (or any CUDA 12 image with Python)
   - Disk: **≥ 120 GB** (weights ~60 GB + vLLM + Lean)
   - Expose SSH
4. SSH into the pod, then:

```bash
git clone https://github.com/YosraBenTaarit/glimmer-verify.git
cd glimmer-verify
export HF_TOKEN=hf_...          # your Hugging Face token
bash scripts/cloud_vllm_pilot.sh
```

5. When it prints `DONE`, download `vllm_cloud_pilot_results.tar.gz` (RunPod
   web UI or `scp`). Then **Stop / terminate the pod immediately**.
6. On your laptop, unpack into `results/vllm_cloud_pilot_v1/` and commit.

## What this adds to a paper that OpenRouter does not

- Server-side prefix-cache hit rate (`/metrics`), not only `cached_tokens`
- KV cache occupancy and preemptions
- Proof that the agent works against **vLLM + official weights**, not only DeepInfra’s API

Keep the OpenRouter 3-seed table as the “n=3, API proxy” result. The cloud
pilot is the “same protocol, reference engine, n=1” confirmation.

## What this run actually did (21 Oct 2026)

Both cells **aborted on B02**. `--max-model-len 8192` rejected a repair prompt
of 8193 tokens (`openai.BadRequestError`). B01 proved in each cell; vLLM APC
and NVML traces are in [`results/vllm_cloud_pilot_v1/`](../results/vllm_cloud_pilot_v1/).
Do not overwrite that folder. A 10-task rerun needs a longer context and an
agent that continues after a 400 — that is a new protocol, documented in the
results README.

`scripts/cloud_vllm_pilot.sh` uses `set -e`, so a cell that does not prove
every task also skips `compare_runs` and the tarball. Pack
`runs/vllm_cloud_pilot_v1` by hand, then **terminate the pod**.

## If something fails

- Architecture unsupported: `export VLLM_EXTRA_ARGS='--model-impl transformers'` and rerun.
- Out of disk: you rented &lt; 120 GB.
- Out of VRAM: you did not get an 80 GB card.
- Slow first start: the 60 GB download is still running; watch `vllm.log`.
