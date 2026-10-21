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
  have hi : i.toNat < n.toNat := (BitVec.ult_iff_toNat_lt).mp hp1
  have h4i : 4 * i.toNat < 4 * n.toNat := Nat.mul_lt_mul_left 4 hi
  have h4i_le : 4 * i.toNat ≤ 4 * n.toNat := Nat.le_of_lt h4i
  have hsum_le : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat :=
    Nat.add_le_add_left h4i_le base.toNat
  have hsum_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    have := Nat.add_le_trans hsum_le hfit
    omega
  have hmul_i : (4 * i).toNat = 4 * i.toNat := by
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hmul_n : (4 * n).toNat = 4 * n.toNat := by
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hadd : (base + 4 * i).toNat = (base.toNat + (4 * i).toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_add]
  rw [hmul_i] at hadd
  have hadd_eq : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    rw [hadd]
    exact Nat.mod_eq_of_lt hsum_lt
  have hbase_add_n : (base + 4 * n).toNat = base.toNat + 4 * n.toNat := by
    simp [BitVec.toNat_add, hmul_n]
    exact Nat.mod_eq_of_lt hfit
  constructor
  · rw [hadd_eq]
    exact Nat.le_add_left base.toNat _
  · rw [hadd_eq]
    have h1 : base.toNat + 4 * i.toNat + 4 ≤ base.toNat + 4 * n.toNat := by
      have : 4 * i.toNat + 4 ≤ 4 * n.toNat := by
        have : 4 * i.toNat < 4 * n.toNat := h4i
        omega
      omega
    exact h1

end GlimmerVerify.Bench
