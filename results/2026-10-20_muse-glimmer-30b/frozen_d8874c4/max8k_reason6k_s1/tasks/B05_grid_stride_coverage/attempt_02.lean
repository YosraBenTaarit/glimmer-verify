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
  have hmod_lt : tid < stride := Nat.mod_lt i hs
  have hmod_eq : tid + stride * k = i := by
    simp [tid, k]
    exact (Nat.mod_add_div i stride).symm
  have hmod_add : tid + k * stride = i := by
    rw [Nat.mul_comm k stride]
    exact hmod_eq
  have hle : tid ≤ i := Nat.mod_le i stride
  exact ⟨tid, hmod_lt, hle, k, hmod_add.symm⟩

end GlimmerVerify.Bench
