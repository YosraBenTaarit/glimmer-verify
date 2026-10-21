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
  have hdiv : i = stride * k + tid := Nat.div_add_mod i stride
  have hle : tid ≤ i := by
    have h1 : tid ≤ tid + stride * k := Nat.le_add_right tid (stride * k)
    have h1' : tid ≤ stride * k + tid := by
      rw [Nat.add_comm tid (stride * k)] at h1
      exact h1
    rw [hdiv] at h1'
    exact h1'
  refine ⟨tid, hmod_lt, hle, ?_⟩
  exact ⟨k, by
    rw [Nat.add_comm tid (stride * k)]
    rw [← Nat.mul_comm k stride]
    exact hdiv⟩

end GlimmerVerify.Bench
