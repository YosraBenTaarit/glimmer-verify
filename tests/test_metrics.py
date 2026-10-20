"""Prometheus parsing, aggregation, and plot rendering."""

import pytest

from src.telemetry.metrics_collector import (
    parse_prometheus_text,
    plot_iterations,
    plot_roofline,
    plot_ttft_vs_retry_turn,
    resolve_metrics,
    summarize,
)

VLLM_SAMPLE = """\
# HELP vllm:kv_cache_usage_perc KV-cache usage. 1 means 100 percent usage.
# TYPE vllm:kv_cache_usage_perc gauge
vllm:kv_cache_usage_perc{engine="0",model_name="meta-models/Muse-Glimmer-30B"} 0.42
# TYPE vllm:num_preemptions counter
vllm:num_preemptions_total{engine="0",model_name="meta-models/Muse-Glimmer-30B"} 3.0
vllm:num_preemptions_created{engine="0",model_name="meta-models/Muse-Glimmer-30B"} 1.7e9
vllm:prefix_cache_queries_total{engine="0",model_name="m"} 1000.0
vllm:prefix_cache_hits_total{engine="0",model_name="m"} 870.0
vllm:time_to_first_token_seconds_sum{engine="0",model_name="m"} 1.5
vllm:time_to_first_token_seconds_count{engine="0",model_name="m"} 6.0
vllm:num_requests_running{engine="0",model_name="m"} 1.0
vllm:num_requests_running{engine="1",model_name="m"} 2.0
"""


def test_parse_and_resolve():
    raw = parse_prometheus_text(VLLM_SAMPLE)
    assert raw["vllm:num_requests_running"] == 3.0
    m = resolve_metrics(raw)
    assert m["kv_cache_usage"] == 0.42
    assert m["preemptions_total"] == 3.0
    assert m["prefix_hits_total"] / m["prefix_queries_total"] == pytest.approx(0.87)
    assert "prefix_hit_rate" not in m


def test_resolve_sglang():
    m = resolve_metrics(parse_prometheus_text('sglang:token_usage{model_name="m"} 0.1\nsglang:cache_hit_rate{model_name="m"} 0.9\n'))
    assert m == {"kv_cache_usage": 0.1, "prefix_hit_rate": 0.9}


TURNS = [
    {"turn": t, "ttft_s": ttft, "prompt_tokens": p, "cached_tokens": c, "server_prefix_hit_rate": ""}
    for t, ttft, p, c in [(1, 0.9, 1000, 0), (2, 0.2, 1400, 1300), (3, 0.25, 1800, 1700), (1, 1.1, 1000, 900), (2, 0.3, 1500, 1400)]
]
TASKS = [
    {"task_id": "a", "proved": "True", "attempts": "3", "max_attempts": "9"},
    {"task_id": "b", "proved": "False", "attempts": "9", "max_attempts": "9"},
]


def test_summarize():
    s = summarize(TURNS, TASKS)
    assert s["proved"] == 1 and s["convergence_rate"] == 0.5
    assert s["attempts_histogram"] == {"3": 1, "unproved": 1}
    assert s["client_prefix_hit_rate_turn1"] == pytest.approx(900 / 2000)
    assert s["client_prefix_hit_rate_turn2plus"] == pytest.approx(4400 / 4700)
    assert s["median_ttft_s_by_turn"]["1"] == pytest.approx(1.0)


def test_plots_render(tmp_path):
    pytest.importorskip("matplotlib")
    assert plot_ttft_vs_retry_turn(TURNS, tmp_path / "ttft.png").stat().st_size > 0
    gpu = [{"sm_util_pct": x, "mem_util_pct": 100 - x, "phase": p} for x, p in [(90, "generate"), (5, "lean_check"), (0, "idle")]]
    assert plot_roofline(gpu, tmp_path / "roofline.png").stat().st_size > 0
    assert plot_iterations(TASKS, tmp_path / "iters.png").stat().st_size > 0
    assert plot_roofline([], tmp_path / "none.png") is None
