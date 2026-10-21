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
  let tid := idx % stride
  have hmod_lt : tid < stride := Nat.mod_lt idx hstride
  have hdiv : idx = stride * (idx / stride) + tid := Nat.div_add_mod idx stride
  have h_eq : idx = tid + idx / stride * stride := by
    rw [Nat.mul_comm (idx / stride) stride] at hdiv
    rw [Nat.add_comm] at hdiv
    exact hdiv
  refine ⟨tid, hmod_lt, ⟨idx / stride, h_eq⟩, ?_⟩
  intro tid' k' htid' heq
  have hmod_tid' : tid' % stride = tid' := Nat.mod_eq_of_lt htid'
  have hmod_k : (k' * stride) % stride = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_mul_right k' stride
  have hmod_rhs : (tid' + k' * stride) % stride = tid' := by
    rw [Nat.add_mod, hmod_tid', hmod_k, Nat.add_zero]
  have hmod_idx : idx % stride = tid' := by
    rw [heq] at hmod_rhs
    rw [← hmod_rhs]
    rfl
  have : tid = tid' := by
    simp [tid] at hmod_idx
    exact hmod_idx.symm
  exact this

end GlimmerVerify.Auto