import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def total (n_slots row_elems : Nat) : Nat := n_slots * row_elems

def writes (stride tid idx : Nat) : Prop :=
  tid < stride ∧ idx ≥ tid ∧ idx % stride = tid

theorem gather_each_output_written_once
    (n_slots row_elems stride : Nat)
    (hstride : 0 < stride)
    (idx : Nat)
    (hidx : idx < n_slots * row_elems) :
    ∃ tid,
      tid < stride ∧ idx ≥ tid ∧ idx % stride = tid ∧
      ∀ tid' < stride, idx ≥ tid' ∧ idx % stride = tid' → tid' = tid := by
  let tid := idx % stride
  have hmod_lt : tid < stride := Nat.mod_lt idx hstride
  have hle : tid ≤ idx := Nat.mod_le idx stride
  refine ⟨tid, hmod_lt, hle, rfl, ?_⟩
  intro tid' hlt' hge
  have hmod' : idx % stride = tid' := hge.2
  have : tid' = idx % stride := hmod'
  rw [this]
  rfl
end GlimmerVerify.Auto