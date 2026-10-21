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
  use i % stride
  constructor
  · exact Nat.mod_lt i hs
  constructor
  · have h := Nat.div_add_mod i stride (Nat.ne_of_gt hs)
    omega
  · use i / stride
    have h := Nat.div_add_mod i stride (Nat.ne_of_gt hs)
    rw [Nat.add_comm]
    exact h

end GlimmerVerify.Bench
