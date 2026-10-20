"""Prompt construction for the proof-repair loop.

Everything here is a pure function of repository files and task data. No timestamps, absolute
paths, random ids, or attempt-independent counters, so the system prompt is byte-identical across
tasks and each task's conversation only ever grows by appending. That is what lets vLLM APC /
SGLang RadixAttention reuse the KV cache of every earlier turn.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from .lean_checker import LeanCheckResult, LeanDiagnostic

MAX_DIAGNOSTICS = 6
MAX_MESSAGE_CHARS = 2500
CONTEXT_LINES = 2

_LEAN_BLOCK_RE = re.compile(r"```(?:lean4?|Lean4?)[^\n]*\n(.*?)```", re.DOTALL)
_ANY_BLOCK_RE = re.compile(r"```[^\n]*\n(.*?)```", re.DOTALL)
_THINK_RE = re.compile(r"<think>.*?</think>", re.DOTALL)


SYSTEM_PROMPT_TEMPLATE = """\
You are a Lean 4 proof engineer verifying GPU inference-runtime code: CUDA kernels, PTX, and C++ host glue.

## Environment
- Lean 4 core only, toolchain `{toolchain}`. There is NO Mathlib: do not import it and do not use Mathlib-only tactics (linarith, nlinarith, norm_num, ring, positivity, aesop, field_simp, exact?).
- Available tactics include: intro, unfold, simp, simp only, split, by_cases, cases, rcases, obtain, induction, constructor, refine, exact, apply, rw, have, show, omega, decide, bv_omega, contradiction, exfalso, `<;>`.
- `omega` decides linear arithmetic over Nat and Int, including `/` and `%` by numeric literals and `2 ^ k` literals. It treats non-linear subterms (`x * y`, `f x`, `x / y` with variable y) as opaque atoms, so unfold definitions before calling it and state facts about atoms with `have`.
- For non-linear facts use core lemmas such as Nat.mod_add_div, Nat.div_add_mod, Nat.add_mul_div_right, Nat.add_mul_mod_self_right, Nat.mod_lt, Nat.mod_le, Nat.mod_eq_of_lt, Nat.div_eq_of_lt, Nat.mul_comm, Nat.add_comm.
- Accepted axioms: propext, Classical.choice, Quot.sound. Proofs using sorry, admit, native_decide, new axioms, set_option, unsafe/implemented_by/extern, or meta-programming commands are rejected.

## Output contract
- Reply with exactly one ```lean code block containing the COMPLETE Lean file. Keep any text outside the block to a sentence or two.
- "complete" tasks: reproduce the template verbatim and replace every `sorry` with a proof. Changing anything else (imports, comments, definitions, statements, namespaces) is rejected. Put helper lemmas inside the proof with `have`.
- "autoformalize" tasks: write definitions that model the given code faithfully, then the requested theorems (exact fully qualified names) with complete proofs. Do not weaken the specification to make it easier to prove.
- After each attempt you receive the Lean compiler's diagnostics for the file you sent. Fix the reported errors and send the full corrected file again.

## Trusted library `GlimmerVerify.PagedKVProofs` (importable, shown verbatim)
```lean
{library}
```
"""

COMPLETE_TASK_TEMPLATE = """\
# Task {task_id} (complete)

## Specification
{spec}

## Code under verification ({source_name})
```{language}
{source}
```

## Template `{template_name}`
Replace every `sorry`; keep all other text exactly as is.
```lean
{template}
```

Required theorems (checked with `#print axioms`): {theorems}
"""

AUTOFORMALIZE_TASK_TEMPLATE = """\
# Task {task_id} (autoformalize)

## Specification
{spec}

## Code under verification ({source_name})
```{language}
{source}
```

Write a complete Lean file that starts with `import GlimmerVerify.PagedKVProofs`, models the code
above, and proves the required theorems. Declare them inside `namespace {namespace}` so that their
fully qualified names are exactly: {theorems}
"""


@dataclass(frozen=True)
class PromptContext:
    toolchain: str
    library_source: str

    @classmethod
    def from_project(cls, lean_project: Path) -> "PromptContext":
        toolchain = (lean_project / "lean-toolchain").read_text(encoding="utf-8").strip()
        library = (lean_project / "GlimmerVerify" / "PagedKVProofs.lean").read_text(encoding="utf-8").strip()
        return cls(toolchain=toolchain, library_source=library)

    def system_prompt(self) -> str:
        return SYSTEM_PROMPT_TEMPLATE.format(toolchain=self.toolchain, library=self.library_source)


def complete_task_prompt(
    *, task_id: str, spec: str, source_name: str, language: str, source: str,
    template_name: str, template: str, theorems: Sequence[str],
) -> str:
    return COMPLETE_TASK_TEMPLATE.format(
        task_id=task_id, spec=spec.strip(), source_name=source_name, language=language,
        source=source.strip(), template_name=template_name, template=template.strip(),
        theorems=", ".join(f"`{t}`" for t in theorems),
    )


def autoformalize_task_prompt(
    *, task_id: str, spec: str, source_name: str, language: str, source: str, theorems: Sequence[str],
) -> str:
    namespaces = {t.rsplit(".", 1)[0] for t in theorems if "." in t}
    namespace = namespaces.pop() if len(namespaces) == 1 else "GlimmerVerify.Auto"
    return AUTOFORMALIZE_TASK_TEMPLATE.format(
        task_id=task_id, spec=spec.strip(), source_name=source_name, language=language,
        source=source.strip(), namespace=namespace, theorems=", ".join(f"`{t}`" for t in theorems),
    )


def extract_lean_code(response: str) -> str | None:
    """The last ```lean block of a response (reasoning tags stripped), or None."""
    text = _THINK_RE.sub("", response)
    blocks = _LEAN_BLOCK_RE.findall(text) or _ANY_BLOCK_RE.findall(text)
    if not blocks:
        return None
    code = blocks[-1].strip("\n")
    return code if code.strip() else None


# ---------------------------------------------------------------------------
# Feedback
# ---------------------------------------------------------------------------

def _excerpt(source_lines: Sequence[str], line: int) -> str:
    lo = max(1, line - CONTEXT_LINES)
    hi = min(len(source_lines), line + CONTEXT_LINES)
    width = len(str(hi))
    out = []
    for n in range(lo, hi + 1):
        marker = ">>" if n == line else "  "
        out.append(f"{marker} {n:>{width}} | {source_lines[n - 1]}")
    return "\n".join(out)


def _format_diagnostic(d: LeanDiagnostic, source_lines: Sequence[str]) -> str:
    message = d.message
    if len(message) > MAX_MESSAGE_CHARS:
        message = message[:MAX_MESSAGE_CHARS] + "\n... (truncated)"
    header = f"{d.severity} at line {d.line}, column {d.column}"
    parts = [f"{header}:", message]
    if 1 <= d.line <= len(source_lines):
        parts += ["", _excerpt(source_lines, d.line)]
    return "\n".join(parts)


def feedback_for_lean(result: LeanCheckResult, checked_source: str, attempt: int, max_attempts: int) -> str:
    source_lines = checked_source.rstrip("\n").split("\n")
    relevant = result.errors + result.sorry_warnings
    sections = [f"Attempt {attempt} of {max_attempts} was rejected by Lean."]
    if result.timed_out:
        sections.append("Lean did not finish within the time limit.")
    for d in relevant[:MAX_DIAGNOSTICS]:
        sections.append(_format_diagnostic(d, source_lines))
    if len(relevant) > MAX_DIAGNOSTICS:
        sections.append(f"({len(relevant) - MAX_DIAGNOSTICS} further diagnostics omitted; fix the ones above first.)")
    for problem in result.problems:
        sections.append(f"audit: {problem}")
    if not relevant and not result.problems and not result.timed_out:
        tail = result.output.strip()[-MAX_MESSAGE_CHARS:]
        sections.append(f"Lean exited with status {result.returncode}:\n{tail}")
    sections.append("Reply with the corrected complete file in a single ```lean block.")
    return "\n\n".join(sections)


def feedback_for_integrity(error: str, attempt: int, max_attempts: int) -> str:
    return (
        f"Attempt {attempt} of {max_attempts} was rejected before compilation: {error}\n\n"
        "Reply with the corrected complete file in a single ```lean block."
    )


def feedback_for_missing_code(attempt: int, max_attempts: int, truncated: bool) -> str:
    reason = (
        "the response hit the output token limit before a complete ```lean block was produced; be more concise"
        if truncated
        else "the response contained no ```lean code block"
    )
    return (
        f"Attempt {attempt} of {max_attempts} was rejected: {reason}.\n\n"
        "Reply with the complete file in a single ```lean block."
    )
