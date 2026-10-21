import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

/-- Number of threads in the grid, i.e. `gridDim * blockDim`. -/
def stride (gridDim blockDim : Nat) : Nat := gridDim * blockDim

/-- `tid` writes `idx` in the grid-stride loop with step `stride` and total `total`. -/
def writes (tid stride total idx : Nat) : Prop :=
  idx < total ∧ ∃ k, idx = tid + k * stride

/-- Existence and uniqueness of the writer for each output index. -/
theorem gather_each_output_written_once
    (stride total idx : Nat)
    (hstride : 0 < stride)
    (hidx : idx < total) :
    (∃ tid, tid < stride ∧ writes tid stride total idx) ∧
    (∀ tid1 tid2, tid1 < stride → tid2 < stride → writes tid1 stride total idx → writes tid2 stride total idx → tid1 = tid2) := by
  constructor
  · let tid := idx % stride
    have hlt : tid < stride := Nat.mod_lt idx hstride
    have hdiv : stride * (idx / stride) + tid = idx := Nat.div_add_mod idx stride
    have hadd : tid + stride * (idx / stride) = idx := by
      rw [Nat.add_comm] at hdiv
      exact hdiv
    have hrep : idx = tid + (idx / stride) * stride := by
      have h : tid + (idx / stride) * stride = idx := by
        rw [Nat.mul_comm (idx / stride) stride]
        exact hadd
      exact h.symm
    exact ⟨tid, hlt, hidx, ⟨idx / stride, hrep⟩⟩
  · intro tid1 tid2 h1 h2 ⟨_, heq1⟩ ⟨_, heq2⟩
    rcases heq1 with ⟨k1, hk1⟩
    rcases heq2 with ⟨k2, hk2⟩
    have hmod1 : idx % stride = tid1 := by
      rw [hk1]
      have : (tid1 + k1 * stride) % stride = tid1 % stride := by
        rw [Nat.add_mod]
        simp [Nat.mul_mod_left]
      rw [this]
      rw [Nat.mod_eq_of_lt h1]
    have hmod2 : idx % stride = tid2 := by
      rw [hk2]
      have : (tid2 + k2 * stride) % stride = tid2 % stride := by
        rw [Nat.add_mod]
        simp [Nat.mul_mod_left]
      rw [this]
      rw [Nat.mod_eq_of_lt h2]
    rw [hmod1] at hmod2
    exact hmod2

end GlimmerVerify.Auto