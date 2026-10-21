import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

theorem gather_each_output_written_once
    (stride total : Nat) (hstride : 0 < stride) (idx : Nat) (hidx : idx < total) :
    ∃ tid : Nat, tid < stride ∧ ∃ k : Nat, idx = tid + k * stride ∧
      ∀ tid' : Nat, tid' < stride → ∃ k' : Nat, idx = tid' + k' * stride → tid' = tid := by
  let tid := idx % stride
  let k := idx / stride
  have htid_lt : tid < stride := Nat.mod_lt idx hstride
  have hdecomp : tid + k * stride = idx := by
    simp [tid, k]
    have h := Nat.div_add_mod idx stride
    rw [Nat.mul_comm] at h
    rw [Nat.add_comm] at h
    exact h
  have hmod_tid : (tid + k * stride) % stride = tid := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_self (by exact Nat.ne_of_gt hstride), Nat.mod_eq_of_lt htid_lt]
  have uniq : ∀ tid' : Nat, tid' < stride → ∃ k' : Nat, idx = tid' + k' * stride → tid' = tid := by
    intro tid' htid'_lt
    intro k' h_eq
    have hmod_tid' : (tid' + k' * stride) % stride = tid' := by
      rw [Nat.add_mod, Nat.mul_mod]
      simp [Nat.mod_self (by exact Nat.ne_of_gt hstride), Nat.mod_eq_of_lt htid'_lt]
    have h1 : (tid + k * stride) % stride = (tid' + k' * stride) % stride := by
      rw [hdecomp, h_eq]
    rw [hmod_tid, hmod_tid'] at h1
    exact h1
  exact ⟨tid, ⟨htid_lt, ⟨k, ⟨hdecomp.symm, uniq⟩⟩⟩⟩

end GlimmerVerify.Auto