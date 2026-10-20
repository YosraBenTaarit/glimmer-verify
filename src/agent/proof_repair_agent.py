"""Muse Glimmer 30B proof-repair loop.

For each task (kernel/PTX source + safety specification [+ Lean template]):

1. Ask the model for a complete Lean 4 file.
2. Rebuild/validate the file (template integrity, lexical policy) and run ``lake env lean`` on it.
3. If Lean rejects it, append the exact diagnostics (line, column, unsolved goals) as the next user
   turn and ask again, up to ``1 + MAX_RETRIES`` attempts.

The message list is append-only: turn k+1's prompt is turn k's prompt + the model's reply + feedback,
so the serving engine's prefix cache covers everything but the newest feedback message.

Usage:
    python -m src.agent.proof_repair_agent                       # every task in the manifest
    python -m src.agent.proof_repair_agent --tasks B03 B06       # id prefixes
    python -m src.agent.proof_repair_agent --source build/ptx/paged_kv_indexer.ptx \\
        --spec "..." --theorem GlimmerVerify.Auto.my_theorem    # ad-hoc autoformalization
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import math
import os
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Protocol, Sequence

from . import prompts
from .glimmer_client import BackendConfig, ChatCompletionResult, ConfigError, GlimmerClient, load_dotenv_if_present
from .lean_checker import (
    CandidateCheck,
    LeanChecker,
    LeanTemplate,
    LeanToolchainError,
    TemplateMismatch,
    validate_freeform,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = REPO_ROOT / "benchmarks" / "unproven_theorems" / "manifest.json"
DEFAULT_LEAN_PROJECT = REPO_ROOT / "src" / "verification" / "GlimmerVerify"
DEFAULT_MAX_RETRIES = 8

_LANGUAGE_BY_SUFFIX = {".cu": "cuda", ".cuh": "cuda", ".ptx": "ptx", ".cpp": "cpp", ".hpp": "cpp", ".c": "c", ".h": "c"}


# ---------------------------------------------------------------------------
# Tasks
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Task:
    id: str
    mode: str  # "complete" | "autoformalize"
    spec: str
    theorems: tuple[str, ...]
    source_name: str
    source_language: str
    source_text: str
    template: LeanTemplate | None = None
    template_name: str | None = None

    def user_prompt(self) -> str:
        if self.mode == "complete":
            assert self.template is not None and self.template_name is not None
            return prompts.complete_task_prompt(
                task_id=self.id, spec=self.spec, source_name=self.source_name, language=self.source_language,
                source=self.source_text, template_name=self.template_name, template=self.template.text,
                theorems=self.theorems,
            )
        return prompts.autoformalize_task_prompt(
            task_id=self.id, spec=self.spec, source_name=self.source_name, language=self.source_language,
            source=self.source_text, theorems=self.theorems,
        )


def read_source(path: Path, snippet: str | None = None) -> str:
    text = path.read_text(encoding="utf-8")
    if snippet is None:
        return text
    m = re.search(
        rf"^[ \t]*// glimmer:snippet-begin {re.escape(snippet)}[ \t]*\n(.*?)^[ \t]*// glimmer:snippet-end",
        text,
        re.MULTILINE | re.DOTALL,
    )
    if m is None:
        raise ValueError(f"snippet {snippet!r} not found in {path}")
    return m.group(1)


def _display_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.name


def load_manifest(manifest_path: Path, task_filters: Sequence[str] = ()) -> tuple[list[Task], Path]:
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    lean_project = (REPO_ROOT / data.get("lean_project", "src/verification/GlimmerVerify")).resolve()
    tasks: list[Task] = []
    for entry in data["tasks"]:
        if task_filters and not any(entry["id"].startswith(f) for f in task_filters):
            continue
        source = entry["source"]
        source_path = (REPO_ROOT / source["path"]).resolve()
        template = template_name = None
        if entry["mode"] == "complete":
            template_path = (manifest_path.parent / entry["template"]).resolve()
            template = LeanTemplate.from_file(template_path)
            template_name = template_path.name
        elif entry["mode"] != "autoformalize":
            raise ValueError(f"task {entry['id']}: unknown mode {entry['mode']!r}")
        snippet = source.get("snippet")
        tasks.append(
            Task(
                id=entry["id"],
                mode=entry["mode"],
                spec=entry["spec"],
                theorems=tuple(entry["theorems"]),
                source_name=_display_path(source_path) + (f" :: {snippet}" if snippet else ""),
                source_language=source.get("language") or _LANGUAGE_BY_SUFFIX.get(source_path.suffix, "text"),
                source_text=read_source(source_path, snippet),
                template=template,
                template_name=template_name,
            )
        )
    if task_filters and not tasks:
        raise ValueError(f"no task id starts with any of {list(task_filters)}")
    return tasks, lean_project


def adhoc_task(
    source: Path, spec: str, theorems: Sequence[str], snippet: str | None, template: Path | None,
    language: str | None,
) -> Task:
    tmpl = LeanTemplate.from_file(template) if template else None
    return Task(
        id=re.sub(r"[^A-Za-z0-9_]+", "_", f"adhoc_{source.stem}_{theorems[0].rsplit('.', 1)[-1]}"),
        mode="complete" if tmpl else "autoformalize",
        spec=spec,
        theorems=tuple(theorems),
        source_name=_display_path(source) + (f" :: {snippet}" if snippet else ""),
        source_language=language or _LANGUAGE_BY_SUFFIX.get(source.suffix, "text"),
        source_text=read_source(source, snippet),
        template=tmpl,
        template_name=template.name if template else None,
    )


# ---------------------------------------------------------------------------
# Agent
# ---------------------------------------------------------------------------

class ChatClient(Protocol):
    def chat(self, messages: Sequence[dict[str, str]]) -> ChatCompletionResult: ...


class Checker(Protocol):
    def check(self, source: str, theorems: Sequence[str], tag: str) -> Any: ...


class NullCollector:
    def begin_turn(self, task_id: str, turn: int) -> None:
        return None

    def end_generation(self, ctx: Any) -> None:
        pass

    def end_turn(self, ctx: Any, completion: ChatCompletionResult, check: CandidateCheck) -> dict[str, Any]:
        return {}

    def set_phase(self, phase: str) -> None:
        pass

    def record_task(self, **kwargs: Any) -> None:
        pass


@dataclass
class TaskResult:
    task_id: str
    mode: str
    proved: bool
    attempts: int
    outcomes: list[str] = field(default_factory=list)
    final_path: str | None = None


class ProofRepairAgent:
    def __init__(
        self,
        client: ChatClient,
        checker: Checker,
        prompt_context: prompts.PromptContext,
        *,
        max_retries: int = DEFAULT_MAX_RETRIES,
        run_dir: Path | None = None,
        run_id: str = "run",
        collector: Any = None,
        log: Any = None,
    ) -> None:
        if max_retries < 0:
            raise ValueError("max_retries must be >= 0")
        self.client = client
        self.checker = checker
        self.system_prompt = prompt_context.system_prompt()
        self.max_attempts = 1 + max_retries
        self.run_dir = run_dir
        self.run_id = run_id
        self.collector = collector or NullCollector()
        self.log = log or (lambda msg: print(msg, file=sys.stderr, flush=True))

    def check_response(self, task: Task, content: str, attempt: int, truncated: bool) -> tuple[CandidateCheck, str]:
        """Validate and compile one response. Returns the check and the feedback for the next turn."""
        code = prompts.extract_lean_code(content)
        if code is None:
            return CandidateCheck("no_code"), prompts.feedback_for_missing_code(attempt, self.max_attempts, truncated)

        if task.mode == "complete":
            assert task.template is not None
            try:
                source = task.template.fill(task.template.extract_proofs(code))
            except TemplateMismatch as exc:
                return (
                    CandidateCheck("integrity_violation", integrity_error=str(exc)),
                    prompts.feedback_for_integrity(str(exc), attempt, self.max_attempts),
                )
        else:
            problems = validate_freeform(code)
            if problems:
                error = "; ".join(problems)
                return (
                    CandidateCheck("integrity_violation", integrity_error=error),
                    prompts.feedback_for_integrity(error, attempt, self.max_attempts),
                )
            source = code

        result = self.checker.check(source, task.theorems, tag=f"{self.run_id}_{task.id}_a{attempt}")
        outcome = "proved" if result.ok else "lean_error"
        feedback = "" if result.ok else prompts.feedback_for_lean(result, source, attempt, self.max_attempts)
        return CandidateCheck(outcome, source=source, result=result), feedback

    def run_task(self, task: Task) -> TaskResult:
        messages: list[dict[str, str]] = [
            {"role": "system", "content": self.system_prompt},
            {"role": "user", "content": task.user_prompt()},
        ]
        task_dir = self._task_dir(task.id)
        result = TaskResult(task_id=task.id, mode=task.mode, proved=False, attempts=0)
        transcript: list[dict[str, Any]] = []

        for attempt in range(1, self.max_attempts + 1):
            ctx = self.collector.begin_turn(task.id, attempt)
            self.collector.set_phase("generate")
            completion = self.client.chat(messages)
            self.collector.end_generation(ctx)
            messages.append({"role": "assistant", "content": completion.content})

            self.collector.set_phase("lean_check")
            check, feedback = self.check_response(
                task, completion.content, attempt, truncated=completion.finish_reason == "length"
            )
            self.collector.set_phase("idle")
            row = self.collector.end_turn(ctx, completion, check)

            result.attempts = attempt
            result.outcomes.append(check.outcome)
            transcript.append({
                "attempt": attempt,
                "outcome": check.outcome,
                "integrity_error": check.integrity_error,
                "lean_errors": len(check.result.errors) if check.result else None,
                "lean_elapsed_s": check.result.elapsed_s if check.result else None,
                "ttft_s": completion.ttft_s,
                "prompt_tokens": completion.prompt_tokens,
                "cached_tokens": completion.cached_tokens,
                "completion_tokens": completion.completion_tokens,
                "finish_reason": completion.finish_reason,
                "reasoning_chars": len(completion.reasoning),
                "telemetry": row,
            })
            if task_dir is not None and check.source is not None:
                (task_dir / f"attempt_{attempt:02d}.lean").write_text(check.source, encoding="utf-8")

            self.log(
                f"[{task.id}] attempt {attempt}/{self.max_attempts}: {check.outcome}"
                + (f" ({len(check.result.errors)} error(s))" if check.result and not check.result.ok else "")
                + (f", ttft {completion.ttft_s:.2f}s" if not math.isnan(completion.ttft_s) else "")
                + (
                    f", cached {completion.cached_tokens}/{completion.prompt_tokens} prompt tokens"
                    if completion.cached_tokens is not None and completion.prompt_tokens
                    else ""
                )
            )

            if check.outcome == "proved":
                result.proved = True
                if task_dir is not None and check.source is not None:
                    final = task_dir / "final.lean"
                    final.write_text(check.source, encoding="utf-8")
                    result.final_path = str(final)
                break
            if attempt < self.max_attempts:
                messages.append({"role": "user", "content": feedback})

        if task_dir is not None:
            (task_dir / "conversation.json").write_text(
                json.dumps({"task_id": task.id, "mode": task.mode, "theorems": task.theorems,
                            "messages": messages, "attempts": transcript}, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
        self.collector.record_task(
            task_id=task.id, mode=task.mode, proved=result.proved, attempts=result.attempts,
            max_attempts=self.max_attempts, outcomes=result.outcomes,
        )
        return result

    def run(self, tasks: Sequence[Task]) -> list[TaskResult]:
        return [self.run_task(task) for task in tasks]

    def _task_dir(self, task_id: str) -> Path | None:
        if self.run_dir is None:
            return None
        path = self.run_dir / "tasks" / task_id
        path.mkdir(parents=True, exist_ok=True)
        return path


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    p.add_argument("--tasks", nargs="*", default=[], help="task id prefixes (default: all)")
    p.add_argument("--max-retries", type=int, default=None, help="repair turns after the first attempt (env MAX_RETRIES, default 8)")
    p.add_argument("--run-dir", type=Path, default=None, help="default: runs/<utc-timestamp>_<backend>")
    p.add_argument("--no-telemetry", action="store_true", help="skip Prometheus/NVML collection and CSV output")
    p.add_argument("--print-prompt", action="store_true", help="print the first prompt of each task and exit")
    adhoc = p.add_argument_group("ad-hoc task (instead of the manifest)")
    adhoc.add_argument("--source", type=Path)
    adhoc.add_argument("--snippet")
    adhoc.add_argument("--language")
    adhoc.add_argument("--spec")
    adhoc.add_argument("--theorem", action="append", default=[], help="fully qualified theorem name (repeatable)")
    adhoc.add_argument("--template", type=Path, help="Lean file with `sorry` holes (complete mode)")
    return p.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    load_dotenv_if_present()
    for stream in (sys.stdout, sys.stderr):
        # Prompts and Lean diagnostics contain ≤, →, ∀ ...; a cp1252 Windows console would crash on them.
        if hasattr(stream, "reconfigure"):
            if stream.isatty():
                stream.reconfigure(errors="backslashreplace")
            else:
                stream.reconfigure(encoding="utf-8")

    if args.source is not None:
        if not args.spec or not args.theorem:
            print("--source requires --spec and at least one --theorem", file=sys.stderr)
            return 2
        tasks = [adhoc_task(args.source, args.spec, args.theorem, args.snippet, args.template, args.language)]
        lean_project = DEFAULT_LEAN_PROJECT
    else:
        tasks, lean_project = load_manifest(args.manifest, args.tasks)

    prompt_ctx = prompts.PromptContext.from_project(lean_project)
    if args.print_prompt:
        print(prompt_ctx.system_prompt())
        for task in tasks:
            print("=" * 100)
            print(task.user_prompt())
        return 0

    try:
        config = BackendConfig.from_env()
        checker = LeanChecker(lean_project)
        checker.ensure_built()
    except (ConfigError, LeanToolchainError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    max_retries = args.max_retries if args.max_retries is not None else int(os.environ.get("MAX_RETRIES", DEFAULT_MAX_RETRIES))
    run_id = _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + f"_{config.server_kind}"
    run_dir = args.run_dir or (REPO_ROOT / "runs" / run_id)
    run_dir.mkdir(parents=True, exist_ok=True)

    collector = None
    if not args.no_telemetry:
        from ..telemetry.metrics_collector import MetricsCollector

        collector = MetricsCollector.from_config(run_dir, run_id=run_id, config=config)

    agent = ProofRepairAgent(
        GlimmerClient(config), checker, prompt_ctx,
        max_retries=max_retries, run_dir=run_dir, run_id=run_id, collector=collector,
    )
    print(f"run {run_id}: {len(tasks)} task(s), backend={config.backend} ({config.server_kind}), "
          f"model={config.model}, attempts/task={agent.max_attempts}", file=sys.stderr)
    try:
        results = agent.run(tasks)
    finally:
        summary = collector.close() if collector is not None else None

    (run_dir / "results.json").write_text(json.dumps([asdict(r) for r in results], indent=2), encoding="utf-8")
    proved = sum(r.proved for r in results)
    print(f"\nproved {proved}/{len(results)} task(s); artifacts in {run_dir}", file=sys.stderr)
    for r in results:
        status = f"proved in {r.attempts}" if r.proved else f"unproved after {r.attempts}"
        print(f"  {r.task_id:<34} {status} attempt(s)", file=sys.stderr)
    if summary:
        hit = summary.get("client_prefix_hit_rate_turn2plus")
        if hit is not None:
            print(f"client prefix-cache hit rate (turns >= 2): {hit:.1%}", file=sys.stderr)
    return 0 if proved == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
