| Metric | append (n=1) | last_error (n=1) |
|---|---|---|
| Proved (of 10) | 1.0 ± 0.0 | 1.0 ± 0.0 |
| First-try proofs | 0.0 ± 0.0 | 1.0 ± 0.0 |
| Repair rate (proved after failing turn 1) | 100% ± 0% | – |
| Attempts to proof, repaired tasks | 2.0 ± 0.0 | – |
| Prefix-cache hit rate, turn 1 | 0% ± 0% | 100% ± 0% |
| Prefix-cache hit rate, turns ≥ 2 | 55% ± 0% | – |
| Cost per run (USD) | 0.000 ± 0.000 | 0.000 ± 0.000 |
| Cost per proved theorem (USD) | 0.0000 ± 0.0000 | 0.0000 ± 0.0000 |
| Attempts per run | 3 ± 0 | 2 ± 0 |

Attempt outcomes (summed over seeds):

| Outcome | append | last_error |
|---|---|---|
| lean_error | 2 (67%) | 0 (0%) |
| no_code_truncated | 0 (0%) | 1 (50%) |
| proved | 1 (33%) | 1 (50%) |

Seeds that proved each task:

| Task | append | last_error |
|---|---|---|
| B01_ptx_bounds_no_wrap | 1/1 | 1/1 |

Providers: append: {'unknown': 3}; last_error: {'unknown': 2}
Commits: (not recorded on the pod)
Total cost: append: \.000; last_error: \.000

Note: only B01 completed. Both cells aborted on B02 when the next prompt was 8193 tokens against --max-model-len 8192. See README.md.
