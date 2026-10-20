"""Checks candidate Lean files with ``lake env lean`` and decides whether a proof is accepted.

A candidate is accepted only if all of the following hold:

1. *Integrity* (template tasks): it equals the template with each ``sorry`` hole replaced, up to
   comments, whitespace, and writing a hole's ``by sorry`` as a term-mode proof. The file that is
   checked is rebuilt from the template's own text, so definitions and statements cannot drift.
2. *Lexical policy*: proofs contain no ``sorry``/``admit``/``native_decide``/new axioms/option or
   meta-programming escapes (comments and strings are ignored).
3. *Compilation*: Lean reports no errors and no ``declaration uses `sorry` `` warnings.
4. *Axiom audit*: ``#print axioms`` for every required theorem lists only Lean's standard axioms.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator, Sequence

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

PROOF_FORBIDDEN = frozenset({
    "sorry", "admit", "native_decide", "axiom", "unsafe", "implemented_by", "extern", "set_option",
    "run_tac", "run_cmd", "run_elab", "ofReduceBool", "ofReduceNat", "macro", "macro_rules", "syntax",
    "elab", "elab_rules", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "instance",
    "opaque", "partial",
})
FREEFORM_FORBIDDEN = frozenset({
    "sorry", "admit", "native_decide", "axiom", "unsafe", "implemented_by", "extern", "set_option",
    "run_tac", "run_cmd", "run_elab", "ofReduceBool", "ofReduceNat",
})
FREEFORM_IMPORT_ROOTS = ("GlimmerVerify", "Init", "Std", "Lean")

_DIAG_RE = re.compile(
    r"^(?P<file>.+?\.lean):(?P<line>\d+):(?P<col>\d+):\s(?P<sev>error|warning|info)"
    r"(?:\((?P<code>[^)]*)\))?:\s?(?P<msg>.*)$"
)
_AXIOMS_RE = re.compile(r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]", re.MULTILINE)
_NO_AXIOMS_RE = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms", re.MULTILINE)
_AUDIT_LINE_RE = re.compile(r"^'[^']+' (depends on axioms|does not depend on any axioms)")
_IDENT_RE = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")


class LeanToolchainError(RuntimeError):
    pass


class TemplateMismatch(ValueError):
    pass


# ---------------------------------------------------------------------------
# Lexing (comment/string aware)
# ---------------------------------------------------------------------------

def iter_code_segments(text: str) -> Iterator[tuple[int, int]]:
    """Yield ``(start, end)`` spans of ``text`` that are code, i.e. outside comments and strings."""
    i, n, start = 0, len(text), 0
    while i < n:
        if text.startswith("--", i):
            if start < i:
                yield start, i
            nl = text.find("\n", i)
            i = n if nl < 0 else nl
            start = i
        elif text.startswith("/-", i):
            if start < i:
                yield start, i
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            start = i
        elif text[i] == '"':
            if start < i:
                yield start, i
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            start = i
        else:
            i += 1
    if start < n:
        yield start, n


def blank_comments(text: str) -> str:
    """``text`` with every comment character except newlines replaced by a space (offsets preserved)."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
        elif text.startswith("/-", i):
            depth, end = 1, i + 2
            while end < n and depth:
                if text.startswith("/-", end):
                    depth, end = depth + 1, end + 2
                elif text.startswith("-/", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        else:
            i += 1
            continue
        for k in range(i, end):
            if out[k] != "\n":
                out[k] = " "
        i = end
    return "".join(out)


def iter_identifiers(text: str) -> Iterator[re.Match[str]]:
    for start, end in iter_code_segments(text):
        yield from _IDENT_RE.finditer(text, start, end)


def forbidden_tokens(text: str, forbidden: Iterable[str]) -> list[str]:
    """Forbidden identifiers (or dotted-name components) that occur in code."""
    banned = frozenset(forbidden)
    found: list[str] = []
    for m in iter_identifiers(text):
        hits = [part for part in m.group(0).split(".") if part in banned]
        for hit in hits:
            if hit not in found:
                found.append(hit)
    return found


def _column(text: str, offset: int) -> int:
    return offset - (text.rfind("\n", 0, offset) + 1)


# ---------------------------------------------------------------------------
# Templates
# ---------------------------------------------------------------------------

def _chunk_pattern(chunk: str, optional_trailing_by: bool = False) -> str:
    tokens = chunk.split()
    if not tokens:
        return r"\s*"
    if optional_trailing_by and len(tokens) > 1 and tokens[-1] == "by":
        return r"\s*" + r"\s+".join(re.escape(t) for t in tokens[:-1]) + r"(?:\s+by(?![\w'!?]))?\s*"
    return r"\s*" + r"\s+".join(re.escape(t) for t in tokens) + r"\s*"


def _ends_with_by(text: str) -> bool:
    return re.search(r"(?:^|\s)by\s*\Z", text) is not None


@dataclass(frozen=True)
class LeanTemplate:
    text: str
    holes: tuple[tuple[int, int], ...]

    @classmethod
    def from_text(cls, text: str) -> "LeanTemplate":
        holes = tuple((m.start(), m.end()) for m in iter_identifiers(text) if m.group(0) == "sorry")
        if not holes:
            raise ValueError("template has no `sorry` holes")
        return cls(text=text, holes=holes)

    @classmethod
    def from_file(cls, path: str | os.PathLike[str]) -> "LeanTemplate":
        return cls.from_text(Path(path).read_text(encoding="utf-8"))

    @property
    def chunks(self) -> list[str]:
        bounds = [0] + [p for hole in self.holes for p in hole] + [len(self.text)]
        return [self.text[bounds[k]:bounds[k + 1]] for k in range(0, len(bounds), 2)]

    def hole_columns(self) -> list[int]:
        return [_column(self.text, start) for start, _ in self.holes]

    def fill(self, proofs: Sequence[str]) -> str:
        if len(proofs) != len(self.holes):
            raise ValueError(f"expected {len(self.holes)} proofs, got {len(proofs)}")
        chunks = self.chunks
        out = [chunks[0]]
        for proof, chunk in zip(proofs, chunks[1:]):
            out += [proof, chunk]
        return "".join(out)

    def extract_proofs(self, candidate: str) -> list[str]:
        """Proof texts for each hole, re-indented to the template's hole columns.

        Raises ``TemplateMismatch`` if anything outside the holes was changed or a proof violates
        the lexical policy.
        """
        chunks = [blank_comments(c) for c in self.chunks]
        candidate = blank_comments(candidate)
        pattern = r"\A" + "(.*?)".join(
            _chunk_pattern(c, optional_trailing_by=k < len(self.holes)) for k, c in enumerate(chunks)
        ) + r"\Z"
        match = re.match(pattern, candidate, re.DOTALL)
        term_mode = [False] * len(self.holes)
        if match is None:
            if len(self.holes) == 1 and not re.search(r"^\s*(theorem|def|namespace|import)\b", candidate, re.M):
                raw = [(candidate.strip(), _column(candidate, len(candidate) - len(candidate.lstrip())))]
            else:
                raise TemplateMismatch(self._diagnose(candidate))
        else:
            raw = [(match.group(k + 1), _column(candidate, match.start(k + 1))) for k in range(len(self.holes))]
            term_mode = [
                _ends_with_by(chunks[k]) and not _ends_with_by(candidate[: match.start(k + 1)])
                for k in range(len(self.holes))
            ]

        proofs: list[str] = []
        for k, ((text, cand_col), hole_col) in enumerate(zip(raw, self.hole_columns()), start=1):
            if term_mode[k - 1]:
                # `:= term` in place of `:= by sorry`: keep the template's `by` and run the term with `exact`.
                body = _reindent(text.rstrip(), cand_col, hole_col + 2)
                proof = "exact\n" + " " * (hole_col + 2) + body if body.strip() else ""
            else:
                proof = _reindent(text.rstrip(), cand_col, hole_col)
            if not proof.strip():
                raise TemplateMismatch(f"hole {k} was left empty")
            bad = forbidden_tokens(proof, PROOF_FORBIDDEN)
            if bad:
                raise TemplateMismatch(f"proof for hole {k} uses forbidden token(s): {', '.join(bad)}")
            for line in proof.split("\n")[1:]:
                if line.strip() and len(line) - len(line.lstrip(" ")) < hole_col:
                    raise TemplateMismatch(
                        f"proof for hole {k} has a line indented less than its tactic block "
                        f"(column {hole_col}): {line.strip()[:80]!r}"
                    )
            proofs.append(proof)
        return proofs

    def _diagnose(self, candidate: str) -> str:
        normalized_candidate = " ".join(candidate.split())
        pos = 0
        chunks = [blank_comments(c) for c in self.chunks]
        for k, chunk in enumerate(chunks):
            m = re.compile(_chunk_pattern(chunk, optional_trailing_by=k < len(self.holes)), re.DOTALL).search(candidate, pos)
            if m is None:
                lines = [ln.strip() for ln in chunk.splitlines() if ln.strip()]
                changed = next((ln for ln in lines if " ".join(ln.split()) not in normalized_candidate), None)
                where = "before the first hole" if k == 0 else f"after hole {k}"
                detail = (
                    f"the template line {changed[:120]!r} is missing or changed"
                    if changed is not None
                    else f"the frozen block {where} was reordered or edited"
                )
                return (
                    f"the template text outside the `sorry` holes was modified: {detail}. "
                    "Keep every declaration and statement exactly as in the template and only replace `sorry` "
                    "(comments and line breaks may differ)."
                )
            pos = m.end()
        return "the template text outside the `sorry` holes was modified; only replace `sorry`."


def _reindent(text: str, from_col: int, to_col: int) -> str:
    lines = text.split("\n")
    delta = to_col - from_col
    out = [lines[0]]
    for line in lines[1:]:
        if delta > 0 and line.strip():
            line = " " * delta + line
        elif delta < 0:
            strip = min(-delta, len(line) - len(line.lstrip(" ")))
            line = line[strip:]
        out.append(line)
    return "\n".join(out)


def validate_freeform(source: str) -> list[str]:
    """Policy violations for a free-form (autoformalize) candidate."""
    problems: list[str] = []
    bad = forbidden_tokens(source, FREEFORM_FORBIDDEN)
    if bad:
        problems.append(f"forbidden token(s): {', '.join(bad)}")
    for m in re.finditer(r"^import\s+(\S+)", source, re.MULTILINE):
        root = m.group(1).split(".")[0]
        if root not in FREEFORM_IMPORT_ROOTS:
            problems.append(f"import {m.group(1)} is not available (allowed roots: {', '.join(FREEFORM_IMPORT_ROOTS)})")
    return problems


# ---------------------------------------------------------------------------
# Lean output
# ---------------------------------------------------------------------------

@dataclass
class LeanDiagnostic:
    line: int
    column: int
    severity: str
    message: str
    code: str | None = None

    @property
    def is_sorry_warning(self) -> bool:
        return self.severity == "warning" and "declaration uses" in self.message and "sorry" in self.message


def parse_diagnostics(output: str) -> list[LeanDiagnostic]:
    diags: list[LeanDiagnostic] = []
    current: LeanDiagnostic | None = None
    for line in output.splitlines():
        m = _DIAG_RE.match(line)
        if m:
            current = LeanDiagnostic(
                line=int(m["line"]), column=int(m["col"]), severity=m["sev"], message=m["msg"], code=m["code"]
            )
            diags.append(current)
        elif _AUDIT_LINE_RE.match(line):
            current = None
        elif current is not None:
            current.message += "\n" + line
    for d in diags:
        d.message = d.message.rstrip()
    return diags


def parse_axioms(output: str) -> dict[str, list[str]]:
    axioms: dict[str, list[str]] = {}
    for m in _AXIOMS_RE.finditer(output):
        axioms[m["name"]] = [a.strip() for a in m["axioms"].split(",") if a.strip()]
    for m in _NO_AXIOMS_RE.finditer(output):
        axioms[m["name"]] = []
    return axioms


@dataclass
class LeanCheckResult:
    ok: bool
    returncode: int | None
    diagnostics: list[LeanDiagnostic]
    axioms: dict[str, list[str]]
    problems: list[str]
    elapsed_s: float
    output: str
    checked_path: Path | None = None
    source_line_count: int = 0
    timed_out: bool = False

    @property
    def errors(self) -> list[LeanDiagnostic]:
        return [d for d in self.diagnostics if d.severity == "error"]

    @property
    def sorry_warnings(self) -> list[LeanDiagnostic]:
        return [d for d in self.diagnostics if d.is_sorry_warning]


def audit(
    output: str,
    returncode: int | None,
    theorems: Sequence[str],
    source_line_count: int,
) -> tuple[bool, list[LeanDiagnostic], dict[str, list[str]], list[str]]:
    diagnostics = parse_diagnostics(output)
    axioms = parse_axioms(output)
    problems: list[str] = []
    for name in theorems:
        if name not in axioms:
            problems.append(f"required theorem `{name}` was not found (declare it with exactly this name)")
            continue
        extra = sorted(set(axioms[name]) - STANDARD_AXIOMS)
        if extra:
            problems.append(f"`{name}` depends on non-standard axioms: {', '.join(extra)}")
    body_errors = [d for d in diagnostics if d.severity == "error" and d.line <= source_line_count]
    audit_errors = [d for d in diagnostics if d.severity == "error" and d.line > source_line_count]
    diagnostics = [d for d in diagnostics if d not in audit_errors]
    ok = (
        returncode == 0
        and not body_errors
        and not audit_errors
        and not any(d.is_sorry_warning for d in diagnostics)
        and not problems
    )
    return ok, diagnostics, axioms, problems


# ---------------------------------------------------------------------------
# Running Lean
# ---------------------------------------------------------------------------

def resolve_lake(lake_cmd: str = "lake") -> str:
    found = shutil.which(lake_cmd)
    if found:
        return found
    elan_bin = Path.home() / ".elan" / "bin"
    for name in ("lake.exe", "lake"):
        candidate = elan_bin / name
        if candidate.is_file():
            return str(candidate)
    raise LeanToolchainError(
        f"`{lake_cmd}` not found; install elan (https://github.com/leanprover/elan) or set LAKE_CMD"
    )


class LeanChecker:
    def __init__(
        self,
        project_dir: str | os.PathLike[str],
        lake_cmd: str | None = None,
        timeout_s: float | None = None,
        scratch_dir: str | os.PathLike[str] | None = None,
    ) -> None:
        self.project_dir = Path(project_dir).resolve()
        if not (self.project_dir / "lakefile.lean").is_file():
            raise LeanToolchainError(f"{self.project_dir} is not a Lake project (no lakefile.lean)")
        self.lake = resolve_lake(lake_cmd or os.environ.get("LAKE_CMD", "lake"))
        self.timeout_s = timeout_s if timeout_s is not None else float(os.environ.get("LEAN_TIMEOUT_S", "300"))
        self.scratch_dir = Path(scratch_dir) if scratch_dir else self.project_dir / ".glimmer_scratch"
        self._built = False

    def ensure_built(self) -> None:
        if self._built:
            return
        proc = subprocess.run(
            [self.lake, "build"],
            cwd=self.project_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=max(self.timeout_s, 1800.0),
        )
        if proc.returncode != 0:
            raise LeanToolchainError(f"`lake build` failed:\n{proc.stdout}\n{proc.stderr}")
        self._built = True

    def check(self, source: str, theorems: Sequence[str], tag: str) -> LeanCheckResult:
        self.ensure_built()
        self.scratch_dir.mkdir(parents=True, exist_ok=True)
        safe_tag = re.sub(r"[^A-Za-z0-9_]+", "_", tag)
        path = self.scratch_dir / f"Candidate_{safe_tag}.lean"
        body = source.rstrip("\n") + "\n"
        line_count = body.count("\n")
        audit_cmds = "".join(f"#print axioms {name}\n" for name in theorems)
        path.write_text(body + "\n" + audit_cmds, encoding="utf-8")

        start = time.perf_counter()
        try:
            proc = subprocess.run(
                [self.lake, "env", "lean", str(path)],
                cwd=self.project_dir,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=self.timeout_s,
            )
        except subprocess.TimeoutExpired as exc:
            out = exc.stdout if isinstance(exc.stdout, str) else (exc.stdout or b"").decode("utf-8", "replace")
            return LeanCheckResult(
                ok=False,
                returncode=None,
                diagnostics=parse_diagnostics(out),
                axioms={},
                problems=[f"Lean timed out after {self.timeout_s:.0f}s (avoid heavy `simp`/`decide` on large terms)"],
                elapsed_s=time.perf_counter() - start,
                output=out,
                checked_path=path,
                source_line_count=line_count,
                timed_out=True,
            )
        elapsed = time.perf_counter() - start
        output = proc.stdout + (("\n" + proc.stderr) if proc.stderr.strip() else "")
        ok, diagnostics, axioms, problems = audit(output, proc.returncode, theorems, line_count)
        return LeanCheckResult(
            ok=ok,
            returncode=proc.returncode,
            diagnostics=diagnostics,
            axioms=axioms,
            problems=problems,
            elapsed_s=elapsed,
            output=output,
            checked_path=path,
            source_line_count=line_count,
        )


@dataclass
class CandidateCheck:
    """Outcome of preparing and checking one model response."""

    outcome: str  # "proved" | "lean_error" | "integrity_violation" | "no_code"
    source: str | None = None
    result: LeanCheckResult | None = None
    integrity_error: str | None = None
    extra: dict[str, object] = field(default_factory=dict)
