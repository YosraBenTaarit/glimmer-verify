import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

/-- Thread identifier in the grid-stride loop. -/
def threadId (blockIdx blockDim threadIdx : Nat) : Nat :=
  blockIdx * blockDim + threadIdx

/-- Stride of the grid-stride loop. -/
def stride (gridDim blockDim : Nat) : Nat :=
  gridDim * blockDim

/-- The set of output indices written by a thread `t` with stride `s` up to `total`. -/
def writes (t s total idx : Nat) : Prop :=
  ∃ k : Nat, idx = t + k * s ∧ idx < total

/-- Existence of a writer for every output index. -/
theorem gather_exists_writer (s total idx : Nat) (hs : 0 < s) (hidx : idx < total) :
    ∃ t : Nat, t < s ∧ writes t s total idx := by
  have hmod : idx % s < s := Nat.mod_lt idx hs
  refine ⟨idx % s, hmod, ?_⟩
  exact ⟨idx / s, by
    have h := Nat.mod_add_div idx s
    rw [Nat.mul_comm s (idx / s)] at h
    rw [h]
    exact ⟨rfl, hidx⟩⟩

/-- Uniqueness of the writer among threads `t < s`. -/
theorem gather_writer_unique (s total idx t1 t2 k1 k2 : Nat)
    (hs : 0 < s)
    (ht1 : t1 < s) (ht2 : t2 < s)
    (h1 : idx = t1 + k1 * s) (h2 : idx = t2 + k2 * s) :
    t1 = t2 := by
  have hmod1 : idx % s = t1 := by
    rw [h1]
    have h := Nat.add_mod (t1) (k1 * s) s
    simp [Nat.mul_mod_left, Nat.mod_eq_of_lt ht1] at h
    rw [h]
  have hmod2 : idx % s = t2 := by
    rw [h2]
    have h := Nat.add_mod (t2) (k2 * s) s
    simp [Nat.mul_mod_left, Nat.mod_eq_of_lt ht2] at h
    rw [h]
  omega

/-- Combined existence and uniqueness for the grid-stride gather kernel. -/
theorem gather_each_output_written_once (gridDim blockDim total idx : Nat)
    (hs : 0 < stride gridDim blockDim)
    (hidx : idx < total) :
    (∃ t : Nat, t < stride gridDim blockDim ∧ writes t (stride gridDim blockDim) total idx) ∧
    (∀ t1 t2 k1 k2,
        t1 < stride gridDim blockDim →
        t2 < stride gridDim blockDim →
        idx = t1 + k1 * stride gridDim blockDim →
        idx = t2 + k2 * stride gridDim blockDim →
        t1 = t2) := by
  constructor
  · exact gather_exists_writer (stride gridDim blockDim) total idx hs hidx
  · intro t1 t2 k1 k2 ht1 ht2 h1 h2
    exact gather_writer_unique (stride gridDim blockDim) total idx t1 t2 k1 k2 hs ht1 ht2 h1 h2

end GlimmerVerify.Auto