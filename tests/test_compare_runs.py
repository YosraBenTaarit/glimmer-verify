"""Aggregation of several runs into the evaluation table."""

import csv
import json

from src.telemetry.compare_runs import aggregate, render_markdown, summarize_run

TURN_COLS = ["task_id", "turn", "outcome", "finish_reason", "prompt_tokens", "cached_tokens", "completion_tokens",
             "cost_usd", "provider"]


def make_run(root, name, config, seed, tasks, turns):
    d = root / name
    d.mkdir()
    (d / "experiment.json").write_text(json.dumps({"config": config, "seed": seed, "commit": "abc"}), encoding="utf-8")
    with (d / "tasks.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, ["task_id", "proved", "attempts"])
        w.writeheader()
        w.writerows({"task_id": t, "proved": str(p), "attempts": a} for t, p, a in tasks)
    with (d / "turns.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, TURN_COLS)
        w.writeheader()
        w.writerows(dict(zip(TURN_COLS, t)) for t in turns)
    return d


def test_summarize_and_aggregate(tmp_path):
    a = make_run(tmp_path, "a_s1", "a", 1, [("T1", True, 1), ("T2", True, 3), ("T3", False, 2)], [
        ("T1", 1, "proved", "stop", 100, 0, 10, 0.01, "P"),
        ("T2", 1, "no_code", "length", 100, 50, 10, 0.01, "P"),
        ("T2", 2, "no_code", "stop", 120, 100, 4, 0.01, "P"),
        ("T2", 3, "proved", "stop", 140, 120, 10, 0.01, "P"),
        ("T3", 1, "lean_error", "stop", 100, 0, 10, 0.01, "P"),
        ("T3", 2, "lean_error", "stop", 140, 100, 10, 0.01, "P"),
    ])
    r = summarize_run(a)
    assert (r["proved"], r["first_try"], r["failed_first_try"], r["repaired"]) == (2, 1, 2, 1)
    assert r["repair_turns_mean"] == 3
    assert abs(r["hit_rate_turn2plus"] - 320 / 400) < 1e-9
    assert abs(r["cost_per_proof_usd"] - 0.03) < 1e-9
    assert r["causes"] == {"proved": 2, "no_code_truncated": 1, "no_code_other": 1, "lean_error": 2}

    make_run(tmp_path, "a_s2", "a", 2, [("T1", False, 1), ("T2", False, 1), ("T3", False, 1)],
             [("T1", 1, "lean_error", "stop", 100, 0, 10, 0.01, "P")])
    agg = aggregate([r, summarize_run(tmp_path / "a_s2")])
    assert agg["a"]["proved"] == (1.0, 2 ** 0.5)
    assert agg["a"]["per_task_proved"] == {"T1": 1, "T2": 1, "T3": 0}
    table = render_markdown(agg)
    assert "| Proved (of 10) | 1.0 ± 1.4 |" in table and "| T3 | 0/2 |" in table
