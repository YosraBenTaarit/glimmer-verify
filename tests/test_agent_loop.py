"""Repair-loop behaviour with a scripted model (no network)."""

import csv
import json
import os
from pathlib import Path

import pytest

from src.agent import prompts
from src.agent.glimmer_client import (
    BackendConfig,
    ChatCompletionResult,
    ConfigError,
    ContextOverflowError,
    _is_context_overflow,
    load_dotenv_if_present,
)
from src.agent.lean_checker import LeanCheckResult, LeanDiagnostic
from src.agent.proof_repair_agent import ProofRepairAgent, load_manifest, view_messages
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


def test_view_messages_keeps_stable_prefix():
    hist = [
        {"role": "system", "content": "S"},
        {"role": "user", "content": "T"},
        {"role": "assistant", "content": ""},
        {"role": "user", "content": "fb1"},
        {"role": "assistant", "content": "proof2"},
        {"role": "user", "content": "fb2"},
    ]
    assert view_messages(hist, "append") == hist
    last = view_messages(hist, "last_error")
    assert last[:2] == hist[:2] and last[2:] == hist[4:]
    dropped = view_messages(hist, "drop_truncated")
    assert dropped[:2] == hist[:2] and dropped[2:] == hist[4:]
    with pytest.raises(ValueError):
        view_messages(hist, "something_else")


def test_last_error_does_not_resend_earlier_failures(task_b04, prompt_ctx):
    wrong = task_b04.template.text.replace("sorry", "simp")
    right = task_b04.template.text.replace("sorry", "unfold elemAddr globalIdx\n  omega")
    client = ScriptedClient([lean_block(wrong), lean_block(wrong), lean_block(right)])
    agent = ProofRepairAgent(client, FakeChecker(), prompt_ctx, max_retries=8, memory="last_error")
    result = agent.run_task(task_b04)
    assert result.proved and result.attempts == 3
    assert [m["role"] for m in client.calls[0]] == ["system", "user"]
    assert client.calls[1][:2] == client.calls[0][:2]
    assert client.calls[1][2]["content"] == lean_block(wrong)
    assert len(client.calls[2]) == 4 and client.calls[2][:2] == client.calls[0][:2]
    assert client.calls[2][2]["content"] == lean_block(wrong)


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


def test_openrouter_provider_pinning():
    base = {"BACKEND": "openrouter", "OPENROUTER_API_KEY": "k"}
    assert BackendConfig.from_env(base).provider_order == ()
    cfg = BackendConfig.from_env({**base, "OPENROUTER_PROVIDER_ORDER": " deepinfra, together ",
                                  "OPENROUTER_ALLOW_FALLBACKS": "false"})
    assert cfg.provider_order == ("deepinfra", "together") and cfg.allow_fallbacks is False
    with pytest.raises(ConfigError):
        BackendConfig.from_env({**base, "OPENROUTER_ALLOW_FALLBACKS": "maybe"})


def test_reasoning_budget_config():
    base = {"BACKEND": "openrouter", "OPENROUTER_API_KEY": "k"}
    assert BackendConfig.from_env({**base, "GLIMMER_REASONING_EFFORT": "Low"}).reasoning_effort == "low"
    cfg = BackendConfig.from_env({**base, "GLIMMER_MAX_TOKENS": "12000", "GLIMMER_REASONING_MAX_TOKENS": "8000"})
    assert cfg.reasoning_max_tokens == 8000
    for bad in ({"GLIMMER_REASONING_EFFORT": "extreme"},
                {"GLIMMER_REASONING_EFFORT": "low", "GLIMMER_REASONING_MAX_TOKENS": "100"},
                {"GLIMMER_MAX_TOKENS": "4096", "GLIMMER_REASONING_MAX_TOKENS": "4096"}):
        with pytest.raises(ConfigError):
            BackendConfig.from_env({**base, **bad})


def test_inspect_run(tmp_path, capsys):
    from src.agent.proof_repair_agent import inspect_run

    task_dir = tmp_path / "tasks" / "B02_x"
    task_dir.mkdir(parents=True)
    lean_fb = "Attempt 1 of 2 was rejected by Lean.\n\nerror at line 3, column 1:\nunknown tactic\n\nReply with ..."
    conv = {
        "task_id": "B02_x", "mode": "complete",
        "messages": [{"role": "system", "content": ""}, {"role": "user", "content": "task"},
                     {"role": "assistant", "content": ""}, {"role": "user", "content": lean_fb},
                     {"role": "assistant", "content": ""}],
        "attempts": [{"attempt": 1, "outcome": "lean_error", "finish_reason": "stop", "completion_tokens": 10},
                     {"attempt": 2, "outcome": "proved", "finish_reason": "stop", "cost_usd": 0.001}],
    }
    (task_dir / "conversation.json").write_text(json.dumps(conv), encoding="utf-8")
    assert inspect_run(tmp_path, ["b02"]) == 0
    out = capsys.readouterr().out
    assert "proved after 2 attempt(s)" in out and "unknown tactic" in out and "0.0010" in out
    assert inspect_run(tmp_path, [], failed_only=True) == 0 and "B02_x" not in capsys.readouterr().out
    assert inspect_run(tmp_path, ["B09"]) == 2


def test_dotenv_fallback_without_python_dotenv(tmp_path, monkeypatch):
    import sys

    env_file = tmp_path / ".env"
    env_file.write_text(
        "# comment\nBACKEND=openrouter\nOPENROUTER_API_KEY= sk-test \nexport OPENROUTER_MODEL='openrouter/free'\n"
        "GLIMMER_TEST_PRESET=from_file\n",
        encoding="utf-8",
    )
    for key in ("BACKEND", "OPENROUTER_API_KEY", "OPENROUTER_MODEL"):
        monkeypatch.delenv(key, raising=False)
    monkeypatch.setenv("GLIMMER_TEST_PRESET", "from_shell")
    monkeypatch.setitem(sys.modules, "dotenv", None)
    load_dotenv_if_present(env_file)
    cfg = BackendConfig.from_env()
    assert cfg.api_key == "sk-test" and cfg.model == "openrouter/free"
    assert os.environ["GLIMMER_TEST_PRESET"] == "from_shell"


def test_is_context_overflow():
    class Exc(Exception):
        status_code = 400

    assert _is_context_overflow(Exc("This model's maximum context length is 8192 tokens"))
    assert not _is_context_overflow(Exc("rate limited"))
    other = Exception("maximum context length is 8192")
    assert not _is_context_overflow(other)


def test_context_overflow_skips_task_and_continues_cell(prompt_ctx):
    tasks, _ = load_manifest(MANIFEST, ["B04", "B06"])
    proved = lean_block(tasks[0].template.text.replace("sorry", "omega"))

    class Client:
        def __init__(self):
            self.n = 0

        def chat(self, messages):
            self.n += 1
            if self.n >= 2:
                raise ContextOverflowError("This model's maximum context length is 8192 tokens")
            return ChatCompletionResult(
                content=proved, reasoning="", finish_reason="stop", response_id="r1",
                prompt_tokens=10, completion_tokens=5, cached_tokens=0,
                ttft_s=0.1, e2e_s=1.0, chunk_gaps_s=[0.02],
            )

    agent = ProofRepairAgent(Client(), FakeChecker(), prompt_ctx, max_retries=1)
    results = agent.run(tasks)
    assert results[0].proved and results[0].task_id == tasks[0].id
    assert not results[1].proved and results[1].outcomes == ["context_overflow"]
