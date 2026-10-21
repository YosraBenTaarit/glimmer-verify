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
  · let tid := idx % stride
    have hmod : tid < stride := Nat.mod_lt idx hstride
    have h := Nat.div_add_mod idx stride
    -- h : stride * (idx / stride) + tid = idx
    have hcomm : tid + stride * (idx / stride) = idx := by
      rw [Nat.add_comm]; exact h
    have hgoal : idx = tid + idx / stride * stride := by
      rw [Nat.mul_comm (idx / stride) stride]
      exact hcomm.symm
    exact ⟨tid, hmod, ⟨idx / stride, hgoal⟩⟩
  · intro tid₁ tid₂ k₁ k₂ h1 h2 h3 h4
    have h1mod : idx % stride = tid₁ := by
      rw [h3]
      have : (tid₁ + k₁ * stride) % stride = tid₁ := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
        simp [Nat.mod_eq_of_lt h1]
      rw [this]
    have h2mod : idx % stride = tid₂ := by
      rw [h4]
      have : (tid₂ + k₂ * stride) % stride = tid₂ := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
        simp [Nat.mod_eq_of_lt h2]
      rw [this]
    exact Eq.trans h1mod.symm h2mod

/-- Convenience lemma: the writer is the remainder modulo stride. -/
theorem gather_writer_is_remainder (stride : Nat) (hstride : 0 < stride)
    (idx : Nat) : (idx % stride) < stride ∧ idx = idx % stride + stride * (idx / stride) := by
  constructor
  · exact Nat.mod_lt idx hstride
  · have h := Nat.div_add_mod idx stride
    rw [Nat.add_comm] at h
    exact h.symm

end GlimmerVerify.Auto