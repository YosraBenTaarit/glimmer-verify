import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

/-- Grid-stride write predicate for the gather kernel. -/
def writes (stride total base idx : Nat) : Prop :=
  base < stride ∧ base < total ∧ idx < total ∧ ∃ k, idx = base + k * stride

/-- Existence of a writer and uniqueness of the writer below `stride`. -/
theorem gather_each_output_written_once (stride total : Nat) (hstride : 0 < stride)
    (idx : Nat) (hidx : idx < total) :
    (∃ tid : Nat, tid < stride ∧ ∃ k, idx = tid + k * stride) ∧
    (∀ tid₁ tid₂ k₁ k₂,
        tid₁ < stride → tid₂ < stride →
        idx = tid₁ + k₁ * stride → idx = tid₂ + k₂ * stride →
        tid₁ = tid₂) := by
  constructor
  · -- existence via Euclidean division
    have hmod : idx % stride < stride := Nat.mod_lt idx hstride
    have hdiv : idx = stride * (idx / stride) + idx % stride := (Nat.div_add_mod idx stride).symm
    refine ⟨idx % stride, hmod, _⟩
    have hcomm : idx = idx % stride + stride * (idx / stride) := by
      rw [hdiv, Nat.add_comm]
    rw [hcomm]
    exact ⟨idx / stride, by rw [Nat.mul_comm]⟩
  · -- uniqueness
    intro tid₁ tid₂ k₁ k₂ h1 h2 h3 h4
    have h1mod : idx % stride = tid₁ := by
      have eq1 : idx % stride = (tid₁ + k₁ * stride) % stride := by rw [h3]
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self] at eq1
      simp [Nat.mod_eq_of_lt h1] at eq1
      exact eq1
    have h2mod : idx % stride = tid₂ := by
      have eq2 : idx % stride = (tid₂ + k₂ * stride) % stride := by rw [h4]
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self] at eq2
      simp [Nat.mod_eq_of_lt h2] at eq2
      exact eq2
    rw [h1mod, h2mod]

/-- Convenience lemma: the writer is the remainder modulo stride. -/
theorem gather_writer_is_remainder (stride : Nat) (hstride : 0 < stride)
    (idx : Nat) : (idx % stride) < stride ∧ idx = idx % stride + stride * (idx / stride) := by
  constructor
  · exact Nat.mod_lt idx hstride
  · have h := (Nat.div_add_mod idx stride).symm
    rw [Nat.add_comm] at h
    exact h

end GlimmerVerify.Auto