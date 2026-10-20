"""Repair-loop behaviour with a scripted model (no network)."""

import csv
import json
from pathlib import Path

import pytest

from src.agent import prompts
from src.agent.glimmer_client import BackendConfig, ChatCompletionResult, ConfigError
from src.agent.lean_checker import LeanCheckResult, LeanDiagnostic
from src.agent.proof_repair_agent import ProofRepairAgent, load_manifest
from src.telemetry.metrics_collector import MetricsCollector

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "benchmarks" / "unproven_theorems" / "manifest.json"
LEAN_PROJECT = ROOT / "src" / "verification" / "GlimmerVerify"


class ScriptedClient:
    def __init__(self, responses):
        self.responses = list(responses)
        self.calls: list[list[dict[str, str]]] = []

    def chat(self, messages):
        self.calls.append([dict(m) for m in messages])
        prompt_tokens = sum(len(m["content"]) for m in messages) // 4
        cached = 0 if len(self.calls) == 1 else int(prompt_tokens * 0.9)
        return ChatCompletionResult(
            content=self.responses.pop(0), reasoning="", finish_reason="stop", response_id=f"r{len(self.calls)}",
            prompt_tokens=prompt_tokens, completion_tokens=40, cached_tokens=cached,
            ttft_s=0.5 if len(self.calls) == 1 else 0.1, e2e_s=1.0, chunk_gaps_s=[0.02] * 39,
        )


class FakeChecker:
    """Accepts a source iff it contains `marker`; otherwise reports one unsolved-goals error."""

    def __init__(self, marker="omega"):
        self.marker = marker
        self.sources: list[str] = []

    def check(self, source, theorems, tag):
        self.sources.append(source)
        if self.marker in source:
            return LeanCheckResult(True, 0, [], {t: ["propext"] for t in theorems}, [], 0.01, "")
        line = source.count("\n") - 1
        diag = LeanDiagnostic(line=line, column=2, severity="error", message="unsolved goals\nn : Nat\n⊢ n < n + 1")
        return LeanCheckResult(False, 1, [diag], {}, [], 0.01, "")


def lean_block(text: str) -> str:
    return f"Here is the file.\n```lean\n{text}\n```"


@pytest.fixture
def task_b04():
    tasks, _ = load_manifest(MANIFEST, ["B04"])
    return tasks[0]


@pytest.fixture
def prompt_ctx():
    return prompts.PromptContext.from_project(LEAN_PROJECT)


def test_prefix_is_append_only(task_b04, prompt_ctx):
    wrong = task_b04.template.text.replace("sorry", "simp")
    right = task_b04.template.text.replace("sorry", "unfold elemAddr globalIdx\n  omega")
    client = ScriptedClient([lean_block(wrong), "no code here", lean_block(right)])
    agent = ProofRepairAgent(client, FakeChecker(), prompt_ctx, max_retries=8)
    result = agent.run_task(task_b04)

    assert result.proved and result.attempts == 3
    assert result.outcomes == ["lean_error", "no_code", "proved"]
    for prev, cur in zip(client.calls, client.calls[1:]):
        assert cur[: len(prev)] == prev, "earlier turns must be re-sent byte-for-byte"
        assert [m["role"] for m in cur[len(prev):]] == ["assistant", "user"]
    assert client.calls[1][2]["content"] == lean_block(wrong)
    assert "unsolved goals" in client.calls[1][3]["content"] and "line" in client.calls[1][3]["content"]


def test_system_prompt_is_task_independent(prompt_ctx):
    tasks, _ = load_manifest(MANIFEST)
    first = {}
    for task in tasks:
        client = ScriptedClient([lean_block(task.template.text if task.template else "x")])
        ProofRepairAgent(client, FakeChecker(marker="\x00"), prompt_ctx, max_retries=0).run_task(task)
        first[task.id] = client.calls[0]
    systems = {calls[0]["content"] for calls in first.values()}
    assert len(systems) == 1
    system = systems.pop()
    assert "theorem paged_kv_isolation" in system and "C:\\" not in system and "/home/" not in system


def test_gives_up_after_max_retries(task_b04, prompt_ctx):
    wrong = lean_block(task_b04.template.text.replace("sorry", "simp"))
    client = ScriptedClient([wrong] * 3)
    result = ProofRepairAgent(client, FakeChecker(), prompt_ctx, max_retries=2).run_task(task_b04)
    assert not result.proved and result.attempts == 3
    assert client.responses == []


def test_integrity_violation_is_fed_back(task_b04, prompt_ctx):
    tampered = task_b04.template.text.replace("(hlane : lane < 32)", "(hlane : lane < 1)").replace("sorry", "omega")
    good = task_b04.template.text.replace("sorry", "unfold elemAddr globalIdx\n  omega")
    client = ScriptedClient([lean_block(tampered), lean_block(good)])
    checker = FakeChecker()
    result = ProofRepairAgent(client, checker, prompt_ctx, max_retries=3).run_task(task_b04)
    assert result.outcomes == ["integrity_violation", "proved"]
    assert len(checker.sources) == 1, "tampered files must never reach Lean"
    assert "outside the `sorry` holes was modified" in client.calls[1][3]["content"]


def test_telemetry_rows(tmp_path, task_b04, prompt_ctx):
    wrong = lean_block(task_b04.template.text.replace("sorry", "simp"))
    right = lean_block(task_b04.template.text.replace("sorry", "unfold elemAddr globalIdx\n  omega"))
    collector = MetricsCollector(tmp_path, run_id="t", backend="local_server", server_kind="vllm", model="m")
    agent = ProofRepairAgent(ScriptedClient([wrong, right]), FakeChecker(), prompt_ctx, max_retries=8,
                             run_dir=tmp_path, collector=collector)
    agent.run_task(task_b04)
    summary = collector.close()

    with (tmp_path / "turns.csv").open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    assert [r["outcome"] for r in rows] == ["lean_error", "proved"]
    assert float(rows[0]["client_prefix_hit_rate"]) == 0.0
    assert float(rows[1]["client_prefix_hit_rate"]) == pytest.approx(0.9, abs=0.01)
    assert rows[0]["server_prefix_hit_rate"] == ""
    assert summary["proved"] == 1 and summary["attempts_histogram"]["2"] == 1
    conversation = json.loads((tmp_path / "tasks" / task_b04.id / "conversation.json").read_text(encoding="utf-8"))
    assert len(conversation["messages"]) == 5
    assert (tmp_path / "tasks" / task_b04.id / "final.lean").is_file()


def test_real_lean_repair(lean_checker, task_b04, prompt_ctx):
    """One wrong proof, then the reference proof, through the real Lean compiler."""
    wrong = lean_block(task_b04.template.text.replace("sorry", "exact ⟨Nat.le_refl _, Nat.le_refl _⟩"))
    reference = (ROOT / "benchmarks" / "reference_solutions" / task_b04.template_name).read_text(encoding="utf-8")
    client = ScriptedClient([wrong, lean_block(reference)])
    result = ProofRepairAgent(client, lean_checker, prompt_ctx, max_retries=3, run_id="pytest").run_task(task_b04)
    assert result.outcomes == ["lean_error", "proved"]
    feedback = client.calls[1][3]["content"]
    assert "error at line" in feedback and ">>" in feedback


def test_backend_config_toggle():
    cfg = BackendConfig.from_env({"BACKEND": "openrouter", "OPENROUTER_API_KEY": "k"})
    assert cfg.base_url == "https://openrouter.ai/api/v1" and cfg.model == "meta/muse-glimmer-30b"
    assert cfg.metrics_url is None
    cfg = BackendConfig.from_env({"BACKEND": "local_server", "LOCAL_SERVER_KIND": "sglang"})
    assert cfg.base_url == "http://localhost:30000/v1" and cfg.metrics_url == "http://localhost:30000/metrics"
    assert cfg.model == "meta-models/Muse-Glimmer-30B"
    cfg = BackendConfig.from_env({"BACKEND": "local_server"})
    assert cfg.base_url == "http://localhost:8000/v1"
    with pytest.raises(ConfigError):
        BackendConfig.from_env({"BACKEND": "openrouter"})
    with pytest.raises(ConfigError):
        BackendConfig.from_env({"BACKEND": "tpu"})
