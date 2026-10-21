import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def globalIdx (blockIdx blockDim threadIdx : Nat) : Nat :=
  blockIdx * blockDim + threadIdx

def stride (gridDim blockDim : Nat) : Nat :=
  gridDim * blockDim

def writes (tid stride idx : Nat) : Prop :=
  ∃ k, idx = tid + k * stride

theorem gather_each_output_written_once
    (total stride idx : Nat)
    (hstride : 0 < stride)
    (hidx : idx < total) :
    ∃ tid,
      tid < stride ∧
      writes tid stride idx ∧
      ∀ tid' k', tid' < stride → idx = tid' + k' * stride → tid' = tid := by
  have hne : stride ≠ 0 := Nat.ne_of_gt hstride
  let tid := idx % stride
  have hmod_lt : tid < stride := Nat.mod_lt idx hne
  have hdiv_add_mod : idx = idx / stride * stride + tid := (Nat.div_add_mod idx stride).symm
  have h_eq : idx = tid + idx / stride * stride := by
    rw [Nat.add_comm]; exact hdiv_add_mod
  refine ⟨tid, hmod_lt, ⟨idx / stride, h_eq⟩, ?_⟩
  intro tid' k' htid' heq
  have hmod_tid' : tid' % stride = tid' := Nat.mod_eq_of_lt htid'
  have hmod_idx : idx % stride = (tid' + k' * stride) % stride := by rw [heq]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self] at hmod_idx
  simp [hmod_tid'] at hmod_idx
  simp [tid] at hmod_idx
  exact hmod_idx

end GlimmerVerify.Auto