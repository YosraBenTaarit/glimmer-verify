# Muse Glimmer 30B on the glimmer-verify benchmark (2026-10-20)

Preliminary results. Every number below can be regenerated from the raw files in this folder.

## Setup

| | |
|---|---|
| Model | `meta/muse-glimmer-30b` via OpenRouter, pinned to the DeepInfra endpoint (BF16); every turn records its provider |
| Harness | commit `d8874c4` (frozen before the measured runs) |
| Tasks | 10: B01–B08 (fill in a `sorry` proof), A01–A02 (write the Lean statement and proof) |
| Loop | 1 attempt + up to 8 repairs; Lean diagnostics are fed back; append-only conversation |
| Sampling | temperature 0.2, top_p 0.95, seeds 1–3 |
| Acceptance | template integrity, no forbidden tokens, `lake env lean` without errors or `sorry`, axiom audit |

The two configurations differ only in the output budget:

- `max4k`: `max_tokens=4096`, reasoning not bounded.
- `max8k_reason6k`: `max_tokens=8192`, OpenRouter `reasoning.max_tokens=6144`.

## Main comparison (`frozen_d8874c4/`, 3 seeds per configuration)

| Metric (mean ± sd over seeds) | max4k | max8k_reason6k |
|---|---|---|
| Proved (of 10) | 5.0 ± 0.0 | 5.0 ± 1.7 |
| First-try proofs | 2.7 ± 0.6 | 1.3 ± 0.6 |
| Repair rate (proved after failing turn 1) | 32% ± 5% | 43% ± 18% |
| Attempts to proof, repaired tasks | 6.8 ± 1.0 | 4.7 ± 0.3 |
| Prefix-cache hit rate, turns ≥ 2 | 89% ± 2% | 83% ± 1% |
| Cost per proved theorem (USD) | 0.040 ± 0.002 | 0.026 ± 0.014 |

| Attempt outcome (all seeds) | max4k | max8k_reason6k |
|---|---|---|
| Proved | 15 (8%) | 15 (8%) |
| Lean error | 61 (32%) | 171 (90%) |
| No code: output limit reached while reasoning | 84 (44%) | 2 (1%) |
| No code: empty 4-token reply | 30 (16%) | 0 |
| Integrity violation | 0 | 2 (1%) |

Full table, per-task results and provider counts: `frozen_d8874c4/table.md`. Per-run and aggregated numbers are in `frozen_d8874c4/summary.json`.

Findings:

1. **Bounding reasoning does not change how many tasks are proved; it changes how.** Unbounded reasoning gives more first-try proofs. Bounded reasoning repairs faster from Lean feedback and costs about 35% less per proof.
2. **With a 4k budget, 60% of attempts produce no proof at all.** With the 6k reasoning cap almost every attempt produces a proof, but 90% of those are rejected by Lean.
3. **The prefix-cache hit rate must be read together with the outcomes.** Empty turns add almost no new tokens, which raises the hit rate. The higher rate under `max4k` partly reflects wasted turns.
4. **B06 and B08 were never proved, in any of the 6 runs.** B02 and A01 were proved once each.

## Empty-reply collapse (`repro_collapse/`)

In the `max4k` runs the model answered 30 times with exactly 4 completion tokens and no content or reasoning. Every one of these came after at least 3 truncated attempts in the same conversation.

To test this, we replayed the exact request that produced such a reply, for B06 and A01 at turn 4 of `max4k_s1`, 6 samples per conversation and condition (seeds 101–106):

| Condition (12 samples each) | Empty / echoed reply | Truncated | Code |
|---|---|---|---|
| Original request | 5 (empty) | 5 | 2 |
| Neutral truncation wording (no "be more concise") | 0 | 12 | 0 |
| Empty assistant turns replaced by a placeholder | 5 (placeholder echoed verbatim) | 6 | 1 |

The model reproduces its previous assistant turn verbatim with zero reasoning tokens: an empty reply when the history holds empty turns, and the placeholder text when it holds the placeholder. This happens only when the feedback says "be more concise" (5/12 vs 0/12, Fisher exact p ≈ 0.02 one-sided).

It is an interaction between a model behaviour and two harness choices: empty assistant turns in the history, and that particular wording. It is not attributable to the model alone.

## Harness issues found and fixed during this study

| Issue | Effect on results |
|---|---|
| Template check rejected comment edits and term-mode proofs (fixed in `493c7eb`) | Pilot only. The 2 affected attempts fail in Lean when re-checked, so the proved count is unchanged; the model received the wrong feedback |
| Requests were load-balanced across providers (DeepInfra / Together) | Pilot only; the frozen runs are pinned |
| `.env` ignored without `python-dotenv`; Windows console encoding crash | No effect on results |

## Caveats

- n = 3 seeds per configuration and 12 samples per replay condition. The differences are consistent observations, not established effects.
- There is one provider deployment (DeepInfra BF16), not Meta's reference serving stack.
- TTFT and inter-token latency are not reported, because the 6 runs shared the provider concurrently.
- Seeds label replicates; provider-side sampling may not be deterministic.
- `pilot/` (unpinned, old checker, 1 run) is kept for completeness and is not part of the comparison.

## Reproduce

```bash
python -m src.telemetry.compare_runs results/2026-10-20_muse-glimmer-30b/frozen_d8874c4
python -m src.agent.proof_repair_agent --inspect results/2026-10-20_muse-glimmer-30b/frozen_d8874c4/max4k_s1 --failed-only
python -m src.experiments.replay_collapse --source results/2026-10-20_muse-glimmer-30b/frozen_d8874c4/max4k_s1 \
    --task B06 --turn 4 --samples 6 --out runs/repro_collapse   # new samples, costs ~$0.07
```

New runs use the same settings as `experiment.json` in each run directory. Total API cost of this study: about $1.45.
