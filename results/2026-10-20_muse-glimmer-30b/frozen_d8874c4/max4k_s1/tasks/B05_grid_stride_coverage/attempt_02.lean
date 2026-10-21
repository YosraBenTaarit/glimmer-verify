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
  let tid := i % stride
  let k := i / stride
  have hmod : tid + stride * k = i := Nat.mod_add_div i stride
  have hmod' : i = tid + k * stride := by
    rw [Nat.mul_comm stride k] at hmod
    exact hmod.symm
  have hlt : tid < stride := Nat.mod_lt i hs
  have hle : tid ≤ i := by
    have : tid ≤ tid + k * stride := Nat.le_add_left tid (k * stride)
    rw [hmod'] at this
    exact this
  exact ⟨tid, hlt, hle, ⟨k, hmod'⟩⟩

end GlimmerVerify.Bench
