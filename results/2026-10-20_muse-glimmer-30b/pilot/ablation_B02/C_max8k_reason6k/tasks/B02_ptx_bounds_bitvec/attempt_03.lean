import GlimmerVerify.PagedKVProofs

/-!
B02: the predicated access over machine words.

`base`, `n` and the lane index `i` are 64-bit registers (`BitVec 64`); `+` and `*` wrap and
`i < n` is the unsigned comparison of `setp.lt.u64`. If the buffer fits in the address space,
the wrapped address of a guarded lane still lies inside the buffer.
-/

namespace GlimmerVerify.Bench

theorem ptx_bounds_bitvec (base n i : BitVec 64) (hfit : base.toNat + 4 * n.toNat < 2 ^ 64)
    (hp1 : i < n) :
    base.toNat ≤ (base + 4 * i).toNat ∧ (base + 4 * i).toNat + 4 ≤ base.toNat + 4 * n.toNat := by
  have hlt : i.toNat < n.toNat := by
    rw [BitVec.ult_iff_toNat_lt] at hp1
    exact hp1
  have h4i_lt : 4 * i.toNat < 4 * n.toNat := by
    have : 0 < 4 := by decide
    exact Nat.mul_lt_mul_of_pos_left hlt this
  have hbase_i_le : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := Nat.add_le_add_left h4i_lt _
  have hbase_i_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hbase_i_le hfit
  have h4i_lt64 : (4 : BitVec 64) * i).toNat = 4 * i.toNat := by
    have hmul_lt : ((4 : BitVec 64) * i).toNat < 2 ^ 64 := by
      have : 4 * i.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hbase_i_lt (Nat.le_add_left _ _)
      exact this
    exact BitVec.toNat_mul (by
      have : (4 : BitVec 64).toNat = 4 := rfl
      rw [this]
      exact h4i_lt64)
  have haddr : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    have hsum_lt : base.toNat + ((4 : BitVec 64) * i).toNat < 2 ^ 64 := by
      rw [hmul]
      exact hbase_i_lt
    have h1 : (base + (4 : BitVec 64) * i).toNat = base.toNat + ((4 : BitVec 64) * i).toNat := by
      exact BitVec.toNat_add hsum_lt
    rw [h1, hmul]
  rw [haddr]
  constructor
  · omega
  · have h4i_plus4 : 4 * i.toNat + 4 ≤ 4 * n.toNat := by
      have : 4 * i.toNat < 4 * n.toNat := h4i_lt
      omega
    omega

end GlimmerVerify.Bench
