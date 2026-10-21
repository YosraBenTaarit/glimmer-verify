import GlimmerVerify.PagedKVProofs

/-!
B05: the grid-stride loop of `paged_kv_gather_kernel` covers every output element.

Thread `tid` executes `for (idx = tid; idx < total; idx += stride)`, i.e. it visits exactly the
indices `tid + k * stride`. Every index `i` is visited by thread `i % stride`, which exists
because `tid < stride = gridDim.x * blockDim.x`.
-/

namespace GlimmerVerify.Bench

/-- Thread `tid` of a grid-stride loop with stride `stride` visits index `i`. -/
def gridStrideVisits (stride tid i : Nat) : Prop :=
  ∃ k, i = tid + k * stride

theorem grid_stride_covers (stride i : Nat) (hs : 0 < stride) :
    ∃ tid, tid < stride ∧ tid ≤ i ∧ gridStrideVisits stride tid i := by
  have hmod_lt : i % stride < stride := Nat.mod_lt i hs
  have hmod_le : i % stride ≤ i := Nat.mod_le i stride
  have hdiv : i = i % stride + (i / stride) * stride := by
    have h := Nat.div_add_mod i stride
    rw [Nat.add_comm] at h
    exact h.symm
  exact ⟨i % stride, hmod_lt, hmod_le, ⟨i / stride, hdiv⟩⟩

end GlimmerVerify.Bench
