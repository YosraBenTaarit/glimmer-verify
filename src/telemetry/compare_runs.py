"""Aggregate several agent runs into the evaluation table (per configuration, mean/sd over seeds).

Each run directory needs ``tasks.csv`` and ``turns.csv`` (written by ``MetricsCollector``) and an
``experiment.json`` with at least ``config`` and ``seed``.

    python -m src.telemetry.compare_runs runs/frozen_d8874c4 [--json out.json]
"""

from __future__ import annotations

import argparse
import csv
import json
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Sequence


def _rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def _num(value: str | None) -> float | None:
    try:
        return float(value) if value not in (None, "") else None
    except ValueError:
        return None


def _hit_rate(turns: Sequence[dict[str, str]]) -> float | None:
    prompt = sum(_num(t["prompt_tokens"]) or 0 for t in turns)
    cached = sum(_num(t["cached_tokens"]) or 0 for t in turns)
    return cached / prompt if prompt else None


def attempt_cause(turn: dict[str, str]) -> str:
    outcome = turn["outcome"]
    if outcome == "no_code":
        return "no_code_truncated" if turn.get("finish_reason") == "length" else "no_code_other"
    return outcome


def summarize_run(run_dir: Path) -> dict[str, Any]:
    exp = json.loads((run_dir / "experiment.json").read_text(encoding="utf-8-sig"))
    tasks = _rows(run_dir / "tasks.csv")
    turns = _rows(run_dir / "turns.csv")
    proved = {t["task_id"]: int(t["attempts"]) for t in tasks if t["proved"] == "True"}
    failed_first = [t for t in tasks if not (t["proved"] == "True" and int(t["attempts"]) == 1)]
    repaired = [t for t in failed_first if t["proved"] == "True"]
    cost = sum(_num(t.get("cost_usd")) or 0 for t in turns)
    return {
        "run": run_dir.name,
        "config": exp["config"],
        "seed": exp.get("seed"),
        "commit": exp.get("commit"),
        "tasks": len(tasks),
        "proved": len(proved),
        "first_try": sum(1 for a in proved.values() if a == 1),
        "failed_first_try": len(failed_first),
        "repaired": len(repaired),
        "repair_turns_mean": statistics.fmean(int(t["attempts"]) for t in repaired) if repaired else None,
        "attempts": len(turns),
        "hit_rate_turn1": _hit_rate([t for t in turns if t["turn"] == "1"]),
        "hit_rate_turn2plus": _hit_rate([t for t in turns if t["turn"] != "1"]),
        "cost_usd": cost,
        "cost_per_proof_usd": cost / len(proved) if proved else None,
        "completion_tokens": sum(_num(t["completion_tokens"]) or 0 for t in turns),
        "causes": dict(Counter(attempt_cause(t) for t in turns)),
        "providers": dict(Counter(t.get("provider") or "unknown" for t in turns)),
        "proved_tasks": proved,
        "all_tasks": [t["task_id"] for t in tasks],
    }


def _mean_sd(values: Sequence[float | None]) -> tuple[float | None, float | None]:
    xs = [v for v in values if v is not None]
    if not xs:
        return None, None
    return statistics.fmean(xs), (statistics.stdev(xs) if len(xs) > 1 else 0.0)


def _fmt(mean: float | None, sd: float | None, pattern: str) -> str:
    if mean is None:
        return "–"
    return f"{pattern.format(mean)} ± {pattern.format(sd)}"


def aggregate(runs: Sequence[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    by_config: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for r in runs:
        by_config[r["config"]].append(r)
    out: dict[str, dict[str, Any]] = {}
    for config, rs in sorted(by_config.items()):
        task_ids = rs[0]["all_tasks"]
        causes: Counter[str] = Counter()
        providers: Counter[str] = Counter()
        for r in rs:
            causes.update(r["causes"])
            providers.update(r["providers"])
        out[config] = {
            "seeds": [r["seed"] for r in rs],
            "commits": sorted({r["commit"] for r in rs}),
            **{
                key: _mean_sd([r[key] for r in rs])
                for key in ("proved", "first_try", "repaired", "repair_turns_mean", "hit_rate_turn1",
                            "hit_rate_turn2plus", "cost_usd", "cost_per_proof_usd", "attempts", "completion_tokens")
            },
            "repair_rate": _mean_sd([r["repaired"] / r["failed_first_try"] if r["failed_first_try"] else None
                                     for r in rs]),
            "total_cost_usd": sum(r["cost_usd"] for r in rs),
            "causes": dict(causes),
            "providers": dict(providers),
            "per_task_proved": {t: sum(t in r["proved_tasks"] for r in rs) for t in task_ids},
        }
    return out


def render_markdown(agg: dict[str, dict[str, Any]]) -> str:
    configs = list(agg)
    n = {c: len(agg[c]["seeds"]) for c in configs}
    lines = ["| Metric | " + " | ".join(f"{c} (n={n[c]})" for c in configs) + " |",
             "|---|" + "---|" * len(configs)]
    rows = [
        ("Proved (of 10)", "proved", "{:.1f}"),
        ("First-try proofs", "first_try", "{:.1f}"),
        ("Repair rate (proved after failing turn 1)", "repair_rate", "{:.0%}"),
        ("Attempts to proof, repaired tasks", "repair_turns_mean", "{:.1f}"),
        ("Prefix-cache hit rate, turn 1", "hit_rate_turn1", "{:.0%}"),
        ("Prefix-cache hit rate, turns ≥ 2", "hit_rate_turn2plus", "{:.0%}"),
        ("Cost per run (USD)", "cost_usd", "{:.3f}"),
        ("Cost per proved theorem (USD)", "cost_per_proof_usd", "{:.4f}"),
        ("Attempts per run", "attempts", "{:.0f}"),
    ]
    for label, key, pattern in rows:
        lines.append(f"| {label} | " + " | ".join(_fmt(*agg[c][key], pattern) for c in configs) + " |")

    causes = sorted({k for c in configs for k in agg[c]["causes"]})
    lines += ["", "Attempt outcomes (summed over seeds):", "",
              "| Outcome | " + " | ".join(configs) + " |", "|---|" + "---|" * len(configs)]
    for cause in causes:
        cells = []
        for c in configs:
            total = sum(agg[c]["causes"].values())
            k = agg[c]["causes"].get(cause, 0)
            cells.append(f"{k} ({k / total:.0%})")
        lines.append(f"| {cause} | " + " | ".join(cells) + " |")

    tasks = list(agg[configs[0]]["per_task_proved"])
    lines += ["", "Seeds that proved each task:", "",
              "| Task | " + " | ".join(configs) + " |", "|---|" + "---|" * len(configs)]
    for t in tasks:
        lines.append(f"| {t} | " + " | ".join(f"{agg[c]['per_task_proved'].get(t, 0)}/{n[c]}" for c in configs) + " |")
    lines += ["", "Providers: " + "; ".join(f"{c}: {agg[c]['providers']}" for c in configs),
              "Commits: " + "; ".join(f"{c}: {', '.join(x[:8] for x in agg[c]['commits'])}" for c in configs),
              "Total cost: " + "; ".join(f"{c}: ${agg[c]['total_cost_usd']:.3f}" for c in configs)]
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("root", type=Path, help="directory containing one sub-directory per run")
    p.add_argument("--json", type=Path, help="also write per-run and aggregated numbers as JSON")
    args = p.parse_args(argv)
    run_dirs = sorted(d for d in args.root.iterdir() if (d / "experiment.json").is_file() and (d / "tasks.csv").is_file())
    if not run_dirs:
        print(f"no runs with experiment.json and tasks.csv under {args.root}", file=sys.stderr)
        return 2
    runs = [summarize_run(d) for d in run_dirs]
    agg = aggregate(runs)
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    print(render_markdown(agg))
    if args.json:
        args.json.write_text(json.dumps({"runs": runs, "aggregate": agg}, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
