| Metric | max4k (n=3) | max8k_reason6k (n=3) |
|---|---|---|
| Proved (of 10) | 5.0 ┬▒ 0.0 | 5.0 ┬▒ 1.7 |
| First-try proofs | 2.7 ┬▒ 0.6 | 1.3 ┬▒ 0.6 |
| Repair rate (proved after failing turn 1) | 32% ┬▒ 5% | 43% ┬▒ 18% |
| Attempts to proof, repaired tasks | 6.8 ┬▒ 1.0 | 4.7 ┬▒ 0.3 |
| Prefix-cache hit rate, turn 1 | 84% ┬▒ 12% | 83% ┬▒ 7% |
| Prefix-cache hit rate, turns ÔëÑ 2 | 89% ┬▒ 2% | 83% ┬▒ 1% |
| Cost per run (USD) | 0.200 ┬▒ 0.012 | 0.115 ┬▒ 0.011 |
| Cost per proved theorem (USD) | 0.0401 ┬▒ 0.0024 | 0.0261 ┬▒ 0.0137 |
| Attempts per run | 63 ┬▒ 2 | 63 ┬▒ 9 |

Attempt outcomes (summed over seeds):

| Outcome | max4k | max8k_reason6k |
|---|---|---|
| integrity_violation | 0 (0%) | 2 (1%) |
| lean_error | 61 (32%) | 171 (90%) |
| no_code_other | 30 (16%) | 0 (0%) |
| no_code_truncated | 84 (44%) | 2 (1%) |
| proved | 15 (8%) | 15 (8%) |

Seeds that proved each task:

| Task | max4k | max8k_reason6k |
|---|---|---|
| B01_ptx_bounds_no_wrap | 3/3 | 3/3 |
| B02_ptx_bounds_bitvec | 0/3 | 1/3 |
| B03_physslot_in_bounds | 3/3 | 2/3 |
| B04_warp_coalesced_segment | 3/3 | 3/3 |
| B05_grid_stride_coverage | 3/3 | 2/3 |
| B06_isolation_bytes | 0/3 | 0/3 |
| B07_physslot_injective | 2/3 | 0/3 |
| B08_striped_allocator_isolated | 0/3 | 0/3 |
| A01_kernel_slot_sentinel | 0/3 | 1/3 |
| A02_gather_written_once | 1/3 | 3/3 |

Providers: max4k: {'DeepInfra': 190}; max8k_reason6k: {'DeepInfra': 190}
Commits: max4k: d8874c48; max8k_reason6k: d8874c48
Total cost: max4k: $0.601; max8k_reason6k: $0.344
