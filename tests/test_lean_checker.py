"""Lean output parsing, template integrity, lexical policy, and real-Lean integration."""

import json
from pathlib import Path

import pytest

from src.agent.lean_checker import (
    LeanTemplate,
    TemplateMismatch,
    audit,
    forbidden_tokens,
    parse_axioms,
    parse_diagnostics,
    validate_freeform,
    PROOF_FORBIDDEN,
)

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "benchmarks" / "unproven_theorems" / "manifest.json"
REFERENCE = ROOT / "benchmarks" / "reference_solutions"

# Verbatim shape of `lake env lean` output on Lean v4.35.0.
SAMPLE_OUTPUT = """\
.glimmer_scratch/Probe.lean:5:8: warning: declaration uses `sorry`
.glimmer_scratch/Probe.lean:9:2: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 0
where
 a := ↑n
C:\\Users\\me\\glimmer\\.glimmer_scratch\\Probe.lean:11:66: error: unsolved goals
case left
a b : Nat
h : a < b
⊢ a ≤ b
'GlimmerVerify.ptx_predicate_bounds_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_sorry' depends on axioms: [sorryAx]
'trivial_thm' does not depend on any axioms
.glimmer_scratch/Probe.lean:17:14: error(lean.unknownIdentifier): Unknown constant `does_not_exist`
"""


def complete_tasks():
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    return [t for t in data["tasks"] if t["mode"] == "complete"]


def test_parse_diagnostics():
    diags = parse_diagnostics(SAMPLE_OUTPUT)
    assert [(d.line, d.column, d.severity) for d in diags] == [
        (5, 8, "warning"), (9, 2, "error"), (11, 66, "error"), (17, 14, "error"),
    ]
    assert diags[0].is_sorry_warning
    assert "counterexample" in diags[1].message and "a := ↑n" in diags[1].message
    assert diags[2].message.startswith("unsolved goals") and diags[2].message.endswith("⊢ a ≤ b")
    assert "depends on axioms" not in diags[2].message
    assert diags[3].code == "lean.unknownIdentifier"


def test_parse_axioms():
    axioms = parse_axioms(SAMPLE_OUTPUT)
    assert axioms["GlimmerVerify.ptx_predicate_bounds_safe"] == ["propext", "Classical.choice", "Quot.sound"]
    assert axioms["probe_sorry"] == ["sorryAx"]
    assert axioms["trivial_thm"] == []


def test_audit_rejects_sorry_axiom_and_missing_theorem():
    ok, _, _, problems = audit(SAMPLE_OUTPUT, 1, ["probe_sorry", "missing_thm"], source_line_count=12)
    assert not ok
    assert any("sorryAx" in p for p in problems)
    assert any("missing_thm" in p for p in problems)
    ok, _, _, problems = audit(
        "'t' depends on axioms: [propext]\n", 0, ["t"], source_line_count=3
    )
    assert ok and not problems


def test_forbidden_tokens_ignore_comments_and_strings():
    text = '-- sorry in a comment\n/- admit /- nested sorry -/ -/\n  have h := "sorry"\n  exact foo.native_decide\n  sorry'
    assert forbidden_tokens(text, PROOF_FORBIDDEN) == ["native_decide", "sorry"]
    assert forbidden_tokens("  simp [h']\n  omega", PROOF_FORBIDDEN) == []


TEMPLATE = """\
import GlimmerVerify.PagedKVProofs

/-! Docs that mention sorry are not holes. -/
namespace X

theorem a (n : Nat) : n + 0 = n := by
  sorry

theorem b (n : Nat) (h : n < 4) : n < 5 := by
  sorry

end X
"""


def test_template_holes_skip_comments():
    t = LeanTemplate.from_text(TEMPLATE)
    assert len(t.holes) == 2
    assert t.hole_columns() == [2, 2]


def test_extract_and_fill_with_whitespace_and_reindent():
    t = LeanTemplate.from_text(TEMPLATE)
    candidate = TEMPLATE.replace("  sorry\n\ntheorem b", "    simp\n\ntheorem b", 1).replace(
        "  sorry\n\nend", "    constructor\n    · omega\n\n\nend", 1
    )
    proofs = t.extract_proofs(candidate)
    assert proofs == ["simp", "constructor\n  · omega"]
    filled = t.fill(proofs)
    assert "sorry" not in filled.split("-/", 1)[1]
    assert filled.startswith(TEMPLATE.split("  sorry")[0])


def test_statement_tampering_is_rejected():
    t = LeanTemplate.from_text(TEMPLATE)
    tampered = TEMPLATE.replace("(h : n < 4)", "(h : n < 5)").replace("sorry", "omega")
    with pytest.raises(TemplateMismatch, match="modified"):
        t.extract_proofs(tampered)


def test_forbidden_proof_is_rejected():
    t = LeanTemplate.from_text(TEMPLATE)
    with pytest.raises(TemplateMismatch, match="native_decide"):
        t.extract_proofs(TEMPLATE.replace("  sorry", "  native_decide"))
    with pytest.raises(TemplateMismatch, match="Docs that mention sorry"):
        t.extract_proofs(TEMPLATE.replace("sorry", "omega"))
    smuggled = TEMPLATE.replace("  sorry\n\ntheorem b", "  simp\n\ntheorem b").replace(
        "  sorry\n\nend", "  omega\ntheorem sneaky : True := trivial\n\nend"
    )
    with pytest.raises(TemplateMismatch, match="indented less"):
        t.extract_proofs(smuggled)


def test_single_hole_bare_proof_is_accepted():
    t = LeanTemplate.from_text("theorem c : 1 = 1 := by\n  sorry\n")
    assert t.extract_proofs("rfl") == ["rfl"]


def test_validate_freeform():
    assert validate_freeform("import GlimmerVerify.PagedKVProofs\ntheorem t : True := trivial") == []
    problems = validate_freeform("import Mathlib\naxiom cheat : False")
    assert any("axiom" in p for p in problems) and any("Mathlib" in p for p in problems)


# ---------------------------------------------------------------------------
# Real Lean (skipped if elan/lake is not installed)
# ---------------------------------------------------------------------------

def test_library_theorems_use_standard_axioms(lean_checker):
    source = "import GlimmerVerify.PagedKVProofs\n"
    result = lean_checker.check(
        source, ["GlimmerVerify.ptx_predicate_bounds_safe", "GlimmerVerify.paged_kv_isolation"], tag="test_library"
    )
    assert result.ok, result.output


@pytest.mark.parametrize("task", complete_tasks(), ids=lambda t: t["id"])
def test_reference_solution_is_accepted(lean_checker, task):
    template = LeanTemplate.from_file(MANIFEST.parent / task["template"])
    solution = (REFERENCE / task["template"]).read_text(encoding="utf-8")
    source = template.fill(template.extract_proofs(solution))
    result = lean_checker.check(source, task["theorems"], tag=f"test_ref_{task['id']}")
    assert result.ok, result.output


@pytest.mark.parametrize("task", complete_tasks()[:2], ids=lambda t: t["id"])
def test_unfilled_template_is_rejected(lean_checker, task):
    template_text = (MANIFEST.parent / task["template"]).read_text(encoding="utf-8")
    result = lean_checker.check(template_text, task["theorems"], tag=f"test_tmpl_{task['id']}")
    assert not result.ok
    assert result.sorry_warnings
    assert any("sorryAx" in p for p in result.problems)


def test_axiom_backstop(lean_checker):
    source = "axiom cheat : False\n\ntheorem bogus : 1 = 2 := cheat.elim\n"
    result = lean_checker.check(source, ["bogus"], tag="test_axiom_backstop")
    assert not result.ok
    assert any("cheat" in p for p in result.problems)
