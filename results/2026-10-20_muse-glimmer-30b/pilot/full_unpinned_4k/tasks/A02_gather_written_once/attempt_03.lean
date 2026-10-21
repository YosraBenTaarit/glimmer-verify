import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def writes (stride tid idx : Nat) : Prop :=
  ∃ k, idx = tid + k * stride

theorem gather_each_output_written_once
    (stride total : Nat) (hstride : 0 < stride) (idx : Nat) (hidx : idx < total) :
    ∃ tid : Nat, tid < stride ∧ ∃ k : Nat, idx = tid + k * stride ∧
      ∀ tid' : Nat, tid' < stride → ∃ k' : Nat, idx = tid' + k' * stride → tid' = tid := by
  let tid := idx % stride
  let k := idx / stride
  have htid_lt : tid < stride := Nat.mod_lt idx hstride
  have hdecomp : idx = tid + k * stride := by
    have h := Nat.div_add_mod idx stride
    rw [Nat.add_comm] at h
    exact h
  use tid, k
  constructor
  · exact htid_lt
  constructor
  · exact hdecomp
  · intro tid' htid'_lt k' h_eq
    have hmod_tid : (tid + k * stride) % stride = tid := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
      simp [Nat.mod_eq_of_lt htid_lt]
    have hmod_tid' : (tid' + k' * stride) % stride = tid' := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
      simp [Nat.mod_eq_of_lt htid'_lt]
    have hmod_eq : (tid + k * stride) % stride = (tid' + k' * stride) % stride := by
      rw [hdecomp, h_eq]
    rw [hmod_tid, hmod_tid'] at hmod_eq
    exact hmod_eq

end GlimmerVerify.Auto