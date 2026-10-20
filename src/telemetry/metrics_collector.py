"""Telemetry for the proof-repair loop.

Per run directory (``runs/<run-id>/``):

``turns.csv``           one row per model call: client TTFT / chunk ITL / TPOT / e2e, token counts,
                        prefix-cache hit rate (client-reported cached tokens and server counter deltas),
                        server KV-cache usage and preemptions, Lean outcome and latency.
``tasks.csv``           one row per task: proved?, attempts-to-convergence.
``server_samples.csv``  1 Hz Prometheus samples (KV usage, running/waiting requests, preemptions).
``gpu_samples.csv``     NVML samples (VRAM, SM busy %, memory-controller busy %, power), tagged with
                        the agent phase (generate / lean_check / idle).
``summary.json``        aggregates used in the paper tables.

``python -m src.telemetry.metrics_collector plot --run-dir runs/<id> [...] --out plots`` renders
``ttft_vs_retry_turn.png``, ``roofline_bandwidth_vs_compute.png`` and ``iterations_to_convergence.png``.

Prometheus metric names differ between vLLM/SGLang versions; each logical metric lists the names
we know of, and metrics a server does not export are left blank rather than guessed.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import re
import statistics
import sys
import threading
import time
import urllib.error
import urllib.request
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

METRIC_CANDIDATES: dict[str, tuple[str, ...]] = {
    "kv_cache_usage": ("vllm:kv_cache_usage_perc", "vllm:gpu_cache_usage_perc", "sglang:token_usage"),
    "preemptions_total": ("vllm:num_preemptions_total", "sglang:num_retracted_reqs_total", "sglang:num_retracted_reqs"),
    "prefix_queries_total": ("vllm:prefix_cache_queries_total", "vllm:gpu_prefix_cache_queries_total"),
    "prefix_hits_total": ("vllm:prefix_cache_hits_total", "vllm:gpu_prefix_cache_hits_total"),
    "prefix_hit_rate": ("vllm:gpu_prefix_cache_hit_rate", "sglang:cache_hit_rate"),
    "ttft_sum": ("vllm:time_to_first_token_seconds_sum", "sglang:time_to_first_token_seconds_sum"),
    "ttft_count": ("vllm:time_to_first_token_seconds_count", "sglang:time_to_first_token_seconds_count"),
    "requests_running": ("vllm:num_requests_running", "sglang:num_running_reqs"),
    "requests_waiting": ("vllm:num_requests_waiting", "sglang:num_queue_reqs"),
}

TURN_FIELDS = [
    "run_id", "task_id", "turn", "backend", "server_kind", "model", "outcome",
    "ttft_s", "itl_mean_s", "itl_p50_s", "itl_p95_s", "tpot_s", "e2e_s",
    "prompt_tokens", "completion_tokens", "cached_tokens", "client_prefix_hit_rate",
    "server_prefix_hit_rate", "server_kv_cache_usage_peak", "server_preemptions_delta", "server_ttft_mean_s",
    "lean_ok", "lean_elapsed_s", "lean_errors", "finish_reason",
    "response_id", "served_model", "provider", "cost_usd",
]
TASK_FIELDS = ["run_id", "task_id", "mode", "proved", "attempts", "max_attempts", "outcomes"]
SERVER_SAMPLE_FIELDS = ["t_s", "phase", "kv_cache_usage", "requests_running", "requests_waiting", "preemptions_total"]
GPU_SAMPLE_FIELDS = ["t_s", "phase", "gpu", "mem_used_mib", "mem_total_mib", "sm_util_pct", "mem_util_pct", "power_w"]

_SAMPLE_RE = re.compile(r"^(?P<name>[a-zA-Z_:][a-zA-Z0-9_:]*)(?:\{(?P<labels>.*)\})?\s+(?P<value>\S+)(?:\s+\S+)?\s*$")


def _log(msg: str) -> None:
    print(f"[telemetry] {msg}", file=sys.stderr, flush=True)


# ---------------------------------------------------------------------------
# Prometheus
# ---------------------------------------------------------------------------

def parse_prometheus_text(text: str) -> dict[str, float]:
    """Sum every sample by metric name (labels such as model_name/engine are aggregated)."""
    totals: dict[str, float] = defaultdict(float)
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = _SAMPLE_RE.match(line)
        if m is None:
            continue
        try:
            value = float(m["value"])
        except ValueError:
            continue
        if math.isnan(value):
            continue
        totals[m["name"]] += value
    return dict(totals)


def resolve_metrics(raw: Mapping[str, float], candidates: Mapping[str, Sequence[str]] = METRIC_CANDIDATES) -> dict[str, float]:
    resolved: dict[str, float] = {}
    for key, names in candidates.items():
        for name in names:
            if name in raw:
                resolved[key] = raw[name]
                break
    return resolved


class PrometheusScraper:
    def __init__(self, url: str, timeout_s: float = 2.0) -> None:
        self.url = url
        self.timeout_s = timeout_s
        self._warned = False

    def scrape(self) -> dict[str, float]:
        try:
            with urllib.request.urlopen(self.url, timeout=self.timeout_s) as resp:
                text = resp.read().decode("utf-8", "replace")
        except (urllib.error.URLError, OSError, ValueError) as exc:
            if not self._warned:
                _log(f"cannot scrape {self.url}: {exc}; server metrics will be blank")
                self._warned = True
            return {}
        return resolve_metrics(parse_prometheus_text(text))


# ---------------------------------------------------------------------------
# Periodic samplers
# ---------------------------------------------------------------------------

class _PeriodicSampler:
    fields: list[str] = []

    def __init__(self, csv_path: Path, interval_s: float, clock_origin: float) -> None:
        self.csv_path = csv_path
        self.interval_s = interval_s
        self.origin = clock_origin
        self.phase = "idle"
        self.samples: list[dict[str, Any]] = []
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._file = None
        self._writer: csv.DictWriter | None = None

    def start(self) -> None:
        self._file = self.csv_path.open("w", newline="", encoding="utf-8")
        self._writer = csv.DictWriter(self._file, fieldnames=self.fields)
        self._writer.writeheader()
        self._thread = threading.Thread(target=self._loop, name=type(self).__name__, daemon=True)
        self._thread.start()

    def stop(self) -> None:
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=5 * self.interval_s + 1)
        self._shutdown()
        if self._file is not None:
            self._file.close()
            self._file = None

    def window(self, t0: float, t1: float) -> list[dict[str, Any]]:
        with self._lock:
            return [s for s in self.samples if t0 - self.origin <= s["t_s"] <= t1 - self.origin]

    def _loop(self) -> None:
        while not self._stop.is_set():
            started = time.perf_counter()
            try:
                rows = self.sample(started - self.origin)
            except Exception as exc:  # a sampler must never kill the run
                _log(f"{type(self).__name__} stopped: {exc}")
                return
            with self._lock:
                self.samples.extend(rows)
                assert self._writer is not None
                self._writer.writerows(rows)
            if self._file is not None:
                self._file.flush()
            self._stop.wait(max(0.0, self.interval_s - (time.perf_counter() - started)))

    def sample(self, t_s: float) -> list[dict[str, Any]]:
        raise NotImplementedError

    def _shutdown(self) -> None:
        pass


class ServerPoller(_PeriodicSampler):
    fields = SERVER_SAMPLE_FIELDS

    def __init__(self, scraper: PrometheusScraper, csv_path: Path, interval_s: float, clock_origin: float) -> None:
        super().__init__(csv_path, interval_s, clock_origin)
        self.scraper = scraper

    def sample(self, t_s: float) -> list[dict[str, Any]]:
        snap = self.scraper.scrape()
        if not snap:
            return []
        return [{"t_s": round(t_s, 4), "phase": self.phase, **{k: snap.get(k) for k in SERVER_SAMPLE_FIELDS[2:]}}]


class NvmlSampler(_PeriodicSampler):
    """NVML utilization is a time fraction: % of the sample period in which >= 1 kernel ran on the
    SMs (sm_util_pct) or the memory controller was busy (mem_util_pct). It is not FLOP/s or GB/s."""

    fields = GPU_SAMPLE_FIELDS

    def __init__(self, csv_path: Path, interval_s: float, clock_origin: float, devices: Sequence[int] | None = None) -> None:
        import pynvml

        super().__init__(csv_path, interval_s, clock_origin)
        self._nvml = pynvml
        pynvml.nvmlInit()
        count = pynvml.nvmlDeviceGetCount()
        indices = list(devices) if devices is not None else list(range(count))
        self._handles = [(i, pynvml.nvmlDeviceGetHandleByIndex(i)) for i in indices]

    def sample(self, t_s: float) -> list[dict[str, Any]]:
        nv = self._nvml
        rows = []
        for index, handle in self._handles:
            mem = nv.nvmlDeviceGetMemoryInfo(handle)
            util = nv.nvmlDeviceGetUtilizationRates(handle)
            try:
                power = nv.nvmlDeviceGetPowerUsage(handle) / 1000.0
            except nv.NVMLError:
                power = None
            rows.append({
                "t_s": round(t_s, 4), "phase": self.phase, "gpu": index,
                "mem_used_mib": round(mem.used / 2**20, 1), "mem_total_mib": round(mem.total / 2**20, 1),
                "sm_util_pct": util.gpu, "mem_util_pct": util.memory, "power_w": power,
            })
        return rows

    def _shutdown(self) -> None:
        try:
            self._nvml.nvmlShutdown()
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Collector
# ---------------------------------------------------------------------------

@dataclass
class TurnContext:
    task_id: str
    turn: int
    t0: float
    before: dict[str, float]
    t_gen_end: float | None = None
    after: dict[str, float] = field(default_factory=dict)


def _delta(after: Mapping[str, float], before: Mapping[str, float], key: str) -> float | None:
    if key in after and key in before:
        return after[key] - before[key]
    return None


def _fmt(value: Any) -> Any:
    if isinstance(value, float):
        return "" if math.isnan(value) else round(value, 6)
    return "" if value is None else value


class MetricsCollector:
    def __init__(
        self,
        run_dir: Path,
        *,
        run_id: str,
        backend: str,
        server_kind: str,
        model: str,
        scraper: PrometheusScraper | None = None,
        server_interval_s: float = 1.0,
        nvml: bool = False,
        nvml_interval_s: float = 0.2,
    ) -> None:
        self.run_dir = Path(run_dir)
        self.run_dir.mkdir(parents=True, exist_ok=True)
        self.run_id, self.backend, self.server_kind, self.model = run_id, backend, server_kind, model
        self.scraper = scraper
        self.origin = time.perf_counter()
        self.turn_rows: list[dict[str, Any]] = []
        self.task_rows: list[dict[str, Any]] = []
        self._first_snapshot = scraper.scrape() if scraper else {}

        self._turns_file = (self.run_dir / "turns.csv").open("w", newline="", encoding="utf-8")
        self._turns = csv.DictWriter(self._turns_file, fieldnames=TURN_FIELDS)
        self._turns.writeheader()
        self._tasks_file = (self.run_dir / "tasks.csv").open("w", newline="", encoding="utf-8")
        self._tasks = csv.DictWriter(self._tasks_file, fieldnames=TASK_FIELDS)
        self._tasks.writeheader()

        self.samplers: list[_PeriodicSampler] = []
        if scraper is not None:
            self.samplers.append(ServerPoller(scraper, self.run_dir / "server_samples.csv", server_interval_s, self.origin))
        if nvml:
            try:
                self.samplers.append(NvmlSampler(self.run_dir / "gpu_samples.csv", nvml_interval_s, self.origin))
            except Exception as exc:
                _log(f"NVML unavailable ({exc}); GPU samples disabled")
        for sampler in self.samplers:
            sampler.start()

    @classmethod
    def from_config(cls, run_dir: Path, *, run_id: str, config: Any, env: Mapping[str, str] | None = None) -> "MetricsCollector":
        env = os.environ if env is None else env
        mode = env.get("GLIMMER_NVML", "auto").strip().lower()
        nvml = mode in ("1", "on", "true") or (mode == "auto" and config.backend == "local_server")
        return cls(
            run_dir,
            run_id=run_id,
            backend=config.backend,
            server_kind=config.server_kind,
            model=config.model,
            scraper=PrometheusScraper(config.metrics_url) if config.metrics_url else None,
            nvml=nvml,
            nvml_interval_s=float(env.get("GLIMMER_NVML_INTERVAL_S", "0.2")),
        )

    # -- agent hooks -------------------------------------------------------------

    def set_phase(self, phase: str) -> None:
        for sampler in self.samplers:
            sampler.phase = phase

    def begin_turn(self, task_id: str, turn: int) -> TurnContext:
        return TurnContext(task_id, turn, time.perf_counter(), self.scraper.scrape() if self.scraper else {})

    def end_generation(self, ctx: TurnContext) -> None:
        ctx.t_gen_end = time.perf_counter()
        ctx.after = self.scraper.scrape() if self.scraper else {}

    def end_turn(self, ctx: TurnContext, completion: Any, check: Any) -> dict[str, Any]:
        before, after = ctx.before, ctx.after
        queries = _delta(after, before, "prefix_queries_total")
        hits = _delta(after, before, "prefix_hits_total")
        if queries:
            server_hit = hits / queries if hits is not None else None
        else:
            server_hit = after.get("prefix_hit_rate")
        ttft_sum, ttft_count = _delta(after, before, "ttft_sum"), _delta(after, before, "ttft_count")

        kv_peak = after.get("kv_cache_usage")
        for sampler in self.samplers:
            if isinstance(sampler, ServerPoller):
                values = [s["kv_cache_usage"] for s in sampler.window(ctx.t0, ctx.t_gen_end or time.perf_counter())
                          if s.get("kv_cache_usage") is not None]
                if values:
                    kv_peak = max(values + ([kv_peak] if kv_peak is not None else []))

        result = getattr(check, "result", None)
        row = {
            "run_id": self.run_id, "task_id": ctx.task_id, "turn": ctx.turn, "backend": self.backend,
            "server_kind": self.server_kind, "model": self.model, "outcome": check.outcome,
            "ttft_s": completion.ttft_s, "itl_mean_s": completion.itl_mean_s,
            "itl_p50_s": completion.itl_quantile_s(0.5), "itl_p95_s": completion.itl_quantile_s(0.95),
            "tpot_s": completion.tpot_s, "e2e_s": completion.e2e_s,
            "prompt_tokens": completion.prompt_tokens, "completion_tokens": completion.completion_tokens,
            "cached_tokens": completion.cached_tokens, "client_prefix_hit_rate": completion.prefix_hit_rate,
            "server_prefix_hit_rate": server_hit, "server_kv_cache_usage_peak": kv_peak,
            "server_preemptions_delta": _delta(after, before, "preemptions_total"),
            "server_ttft_mean_s": (ttft_sum / ttft_count) if ttft_sum is not None and ttft_count else None,
            "lean_ok": result.ok if result is not None else None,
            "lean_elapsed_s": result.elapsed_s if result is not None else None,
            "lean_errors": len(result.errors) if result is not None else None,
            "finish_reason": completion.finish_reason,
            "response_id": completion.response_id,
            "served_model": getattr(completion, "served_model", None),
            "provider": getattr(completion, "provider", None),
            "cost_usd": getattr(completion, "cost_usd", None),
        }
        self.turn_rows.append(row)
        self._turns.writerow({k: _fmt(v) for k, v in row.items()})
        self._turns_file.flush()
        return row

    def record_task(self, *, task_id: str, mode: str, proved: bool, attempts: int, max_attempts: int,
                    outcomes: Sequence[str]) -> None:
        row = {"run_id": self.run_id, "task_id": task_id, "mode": mode, "proved": proved, "attempts": attempts,
               "max_attempts": max_attempts, "outcomes": "|".join(outcomes)}
        self.task_rows.append(row)
        self._tasks.writerow(row)
        self._tasks_file.flush()

    def close(self) -> dict[str, Any]:
        for sampler in self.samplers:
            sampler.stop()
        last = self.scraper.scrape() if self.scraper else {}
        summary = summarize(self.turn_rows, self.task_rows)
        summary.update({"run_id": self.run_id, "backend": self.backend, "server_kind": self.server_kind, "model": self.model})
        queries = _delta(last, self._first_snapshot, "prefix_queries_total")
        hits = _delta(last, self._first_snapshot, "prefix_hits_total")
        summary["server_prefix_hit_rate_run"] = (hits / queries) if queries and hits is not None else None
        summary["server_preemptions_run"] = _delta(last, self._first_snapshot, "preemptions_total")
        (self.run_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
        self._turns_file.close()
        self._tasks_file.close()
        return summary

    def __enter__(self) -> "MetricsCollector":
        return self

    def __exit__(self, *exc: Any) -> None:
        self.close()


# ---------------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------------

def _num(value: Any) -> float | None:
    if value is None or value == "":
        return None
    if isinstance(value, bool):
        return float(value)
    try:
        out = float(value)
    except (TypeError, ValueError):
        return None
    return None if math.isnan(out) else out


def _truthy(value: Any) -> bool:
    return value is True or str(value).strip().lower() in ("true", "1")


def _token_weighted_hit_rate(rows: Iterable[Mapping[str, Any]]) -> float | None:
    cached = prompt = 0.0
    for r in rows:
        c, p = _num(r.get("cached_tokens")), _num(r.get("prompt_tokens"))
        if c is not None and p:
            cached += c
            prompt += p
    return cached / prompt if prompt else None


def summarize(turn_rows: Sequence[Mapping[str, Any]], task_rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    proved = [r for r in task_rows if _truthy(r["proved"])]
    attempts = [int(_num(r["attempts"]) or 0) for r in proved]
    by_turn: dict[int, list[float]] = defaultdict(list)
    for r in turn_rows:
        ttft = _num(r.get("ttft_s"))
        if ttft is not None:
            by_turn[int(_num(r["turn"]) or 0)].append(ttft)
    histogram: dict[str, int] = defaultdict(int)
    for a in attempts:
        histogram[str(a)] += 1
    histogram["unproved"] = len(task_rows) - len(proved)
    return {
        "tasks": len(task_rows),
        "proved": len(proved),
        "convergence_rate": len(proved) / len(task_rows) if task_rows else None,
        "mean_attempts_to_proof": statistics.fmean(attempts) if attempts else None,
        "attempts_histogram": dict(histogram),
        "turns": len(turn_rows),
        "client_prefix_hit_rate_turn1": _token_weighted_hit_rate(r for r in turn_rows if _num(r["turn"]) == 1),
        "client_prefix_hit_rate_turn2plus": _token_weighted_hit_rate(r for r in turn_rows if (_num(r["turn"]) or 0) >= 2),
        "median_ttft_s_by_turn": {str(t): statistics.median(v) for t, v in sorted(by_turn.items())},
        "total_prompt_tokens": sum(_num(r.get("prompt_tokens")) or 0 for r in turn_rows),
        "total_completion_tokens": sum(_num(r.get("completion_tokens")) or 0 for r in turn_rows),
        "total_cost_usd": sum(_num(r.get("cost_usd")) or 0 for r in turn_rows),
        "turns_by_provider": dict(Counter(r.get("provider") or "unknown" for r in turn_rows)),
    }


# ---------------------------------------------------------------------------
# Plots
# ---------------------------------------------------------------------------

def read_csv_rows(paths: Iterable[Path]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        if path.is_file():
            with path.open(newline="", encoding="utf-8") as f:
                rows.extend(csv.DictReader(f))
    return rows


def _pyplot():
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    plt.rcParams.update({"figure.dpi": 150, "savefig.dpi": 200, "font.size": 9, "axes.grid": True, "grid.alpha": 0.3})
    return plt


def plot_ttft_vs_retry_turn(turn_rows: Sequence[Mapping[str, Any]], out: Path) -> Path | None:
    by_turn: dict[int, list[float]] = defaultdict(list)
    for r in turn_rows:
        ttft = _num(r.get("ttft_s"))
        if ttft is not None:
            by_turn[int(_num(r["turn"]) or 0)].append(ttft)
    if not by_turn:
        _log("no TTFT samples; skipping ttft_vs_retry_turn")
        return None
    plt = _pyplot()
    turns = sorted(by_turn)
    med = [statistics.median(by_turn[t]) for t in turns]
    q1 = [statistics.quantiles(by_turn[t], n=4)[0] if len(by_turn[t]) > 1 else by_turn[t][0] for t in turns]
    q3 = [statistics.quantiles(by_turn[t], n=4)[2] if len(by_turn[t]) > 1 else by_turn[t][0] for t in turns]

    fig, ax = plt.subplots(figsize=(5.0, 3.2))
    for t in turns:
        ax.scatter([t] * len(by_turn[t]), by_turn[t], s=8, color="tab:blue", alpha=0.25, linewidths=0)
    ax.fill_between(turns, q1, q3, color="tab:blue", alpha=0.15, label="TTFT IQR")
    ax.plot(turns, med, "o-", color="tab:blue", label="TTFT median")
    ax.set_xlabel("repair turn (1 = initial attempt)")
    ax.set_ylabel("time to first token [s]")
    ax.set_xticks(turns)
    for t, m in zip(turns, med):
        ax.annotate(f"n={len(by_turn[t])}", (t, m), textcoords="offset points", xytext=(0, 6), ha="center", fontsize=6)

    hit_by_turn = {t: _token_weighted_hit_rate(r for r in turn_rows if _num(r["turn"]) == t) for t in turns}
    label = "client prefix-cache hit rate"
    if all(v is None for v in hit_by_turn.values()):
        server = defaultdict(list)
        for r in turn_rows:
            v = _num(r.get("server_prefix_hit_rate"))
            if v is not None:
                server[int(_num(r["turn"]) or 0)].append(v)
        hit_by_turn = {t: statistics.fmean(server[t]) if server[t] else None for t in turns}
        label = "server prefix-cache hit rate"
    lines, labels = ax.get_legend_handles_labels()
    if any(v is not None for v in hit_by_turn.values()):
        ax2 = ax.twinx()
        ax2.grid(False)
        xs = [t for t in turns if hit_by_turn[t] is not None]
        ax2.plot(xs, [100 * hit_by_turn[t] for t in xs], "s--", color="tab:orange", label=label)
        ax2.set_ylabel("prefix-cache hit rate [%]")
        ax2.set_ylim(0, 105)
        l2, lab2 = ax2.get_legend_handles_labels()
        lines, labels = lines + l2, labels + lab2
    ax.legend(lines, labels, loc="upper center", bbox_to_anchor=(0.5, -0.17), ncol=3, fontsize=7, frameon=False)
    ax.set_title("TTFT vs. retry turn (append-only repair conversation)")
    fig.tight_layout()
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out)
    plt.close(fig)
    return out


def plot_roofline(gpu_rows: Sequence[Mapping[str, Any]], out: Path) -> Path | None:
    points = [(_num(r.get("sm_util_pct")), _num(r.get("mem_util_pct")), r.get("phase", "idle")) for r in gpu_rows]
    points = [(x, y, p) for x, y, p in points if x is not None and y is not None]
    if not points:
        _log("no NVML samples (BACKEND=openrouter or no NVIDIA GPU); skipping roofline plot")
        return None
    plt = _pyplot()
    fig, ax = plt.subplots(figsize=(4.4, 4.0))
    colors = {"generate": "tab:red", "lean_check": "tab:green", "idle": "tab:gray"}
    for phase in sorted({p for _, _, p in points}):
        xs = [x for x, _, p in points if p == phase]
        ys = [y for _, y, p in points if p == phase]
        ax.scatter(xs, ys, s=10, alpha=0.45, linewidths=0, color=colors.get(phase, "tab:purple"), label=f"{phase} (n={len(xs)})")
    ax.plot([0, 100], [0, 100], color="black", lw=0.8, ls=":")
    ax.text(8, 92, "memory-bound side", fontsize=7, color="dimgray")
    ax.text(55, 5, "compute-bound side", fontsize=7, color="dimgray")
    ax.set_xlim(0, 102)
    ax.set_ylim(0, 102)
    ax.set_xlabel("SM busy [% of sample period] (NVML)")
    ax.set_ylabel("memory controller busy [% of sample period] (NVML)")
    ax.set_title("Bandwidth vs. compute occupancy by agent phase", fontsize=9)
    ax.legend(fontsize=7, loc="center right")
    fig.tight_layout()
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out)
    plt.close(fig)
    return out


def plot_iterations(task_rows: Sequence[Mapping[str, Any]], out: Path) -> Path | None:
    if not task_rows:
        _log("no task rows; skipping iterations_to_convergence")
        return None
    plt = _pyplot()
    max_attempts = max(int(_num(r.get("max_attempts")) or 0) for r in task_rows) or 1
    counts = [0] * (max_attempts + 1)
    unproved = 0
    for r in task_rows:
        if _truthy(r["proved"]):
            counts[int(_num(r["attempts"]) or 0)] += 1
        else:
            unproved += 1
    fig, ax = plt.subplots(figsize=(5.0, 3.0))
    xs = list(range(1, max_attempts + 1))
    ax.bar(xs, counts[1:], color="tab:green", label="proved")
    ax.bar([max_attempts + 1.5], [unproved], color="tab:red", label="not proved")
    ax.set_xticks(xs + [max_attempts + 1.5])
    ax.set_xticklabels([str(x) for x in xs] + ["✗"])
    ax.set_xlabel("attempts to a Lean-accepted proof")
    ax.set_ylabel("tasks")
    ax.legend(fontsize=7)
    ax.set_title("Iterations to proof convergence")
    fig.tight_layout()
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out)
    plt.close(fig)
    return out


def render_plots(run_dirs: Sequence[Path], out_dir: Path) -> list[Path]:
    turns = read_csv_rows(d / "turns.csv" for d in run_dirs)
    tasks = read_csv_rows(d / "tasks.csv" for d in run_dirs)
    gpu = read_csv_rows(d / "gpu_samples.csv" for d in run_dirs)
    written = [
        plot_ttft_vs_retry_turn(turns, out_dir / "ttft_vs_retry_turn.png"),
        plot_roofline(gpu, out_dir / "roofline_bandwidth_vs_compute.png"),
        plot_iterations(tasks, out_dir / "iterations_to_convergence.png"),
    ]
    return [p for p in written if p is not None]


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="glimmer-verify telemetry tools")
    sub = parser.add_subparsers(dest="cmd", required=True)
    p_plot = sub.add_parser("plot", help="render paper plots from one or more run directories")
    p_plot.add_argument("--run-dir", type=Path, nargs="+", required=True)
    p_plot.add_argument("--out", type=Path, default=Path("plots"))
    p_scrape = sub.add_parser("scrape", help="print the resolved server metrics once")
    p_scrape.add_argument("--url", default="http://localhost:8000/metrics")
    p_scrape.add_argument("--raw", action="store_true", help="print every vllm:/sglang: sample")
    sub.add_parser("nvml", help="print one NVML sample per GPU")
    args = parser.parse_args(argv)

    if args.cmd == "plot":
        missing = [d for d in args.run_dir if not (d / "turns.csv").is_file()]
        if missing:
            print(f"no turns.csv in: {', '.join(map(str, missing))}", file=sys.stderr)
            return 2
        for path in render_plots(args.run_dir, args.out):
            print(path)
        for d in args.run_dir:
            if (d / "summary.json").is_file():
                print(f"{d}: {(d / 'summary.json').read_text(encoding='utf-8')}")
        return 0
    if args.cmd == "scrape":
        if args.raw:
            with urllib.request.urlopen(args.url, timeout=5) as resp:
                raw = parse_prometheus_text(resp.read().decode("utf-8", "replace"))
            for name in sorted(n for n in raw if n.startswith(("vllm:", "sglang:"))):
                print(f"{name} {raw[name]}")
        else:
            print(json.dumps(PrometheusScraper(args.url).scrape(), indent=2))
        return 0
    if args.cmd == "nvml":
        import tempfile

        with tempfile.TemporaryDirectory() as tmp:
            sampler = NvmlSampler(Path(tmp) / "gpu.csv", 1.0, time.perf_counter())
            print(json.dumps(sampler.sample(0.0), indent=2))
            sampler._shutdown()
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(main())
