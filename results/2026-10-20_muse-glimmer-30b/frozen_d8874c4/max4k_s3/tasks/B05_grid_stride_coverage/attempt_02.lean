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
  have hdiv_eq : stride * k + tid = i := Nat.div_add_mod i stride
  have hle : tid ≤ i := by
    have h1 : tid ≤ stride * k + tid := Nat.le_add_right tid (stride * k)
    rw [hdiv_eq] at h1
    exact h1
  have h_eq : i = tid + k * stride := by
    rw [hdiv_eq]
    rw [Nat.mul_comm stride k]
    rw [Nat.add_comm tid (k * stride)]
  refine ⟨tid, hmod_lt, hle, ?_⟩
  exact ⟨k, h_eq⟩

end GlimmerVerify.Bench
