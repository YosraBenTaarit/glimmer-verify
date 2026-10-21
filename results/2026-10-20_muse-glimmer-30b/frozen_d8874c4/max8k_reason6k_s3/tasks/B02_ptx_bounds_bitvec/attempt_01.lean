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
  have hi : i.toNat < n.toNat := (BitVec.lt_iff_toNat_lt).mp hp1
  have h4i_lt_4n : 4 * i.toNat < 4 * n.toNat := Nat.mul_lt_mul_left 4 hi
  have hbase_add_4i_le : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := Nat.add_le_add_left h4i_lt_4n base.toNat
  have hbase_add_4i_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    calc
      base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := hbase_add_4i_le
      _ < 2 ^ 64 := hfit
  have h4i_toNat : (4 * i).toNat = 4 * i.toNat := by
    have hmul_lt : 4 * i.toNat < 2 ^ 64 := by
      have : i.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hi (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) 64)) (by decide))) (by decide))
      omega
    simpa [BitVec.toNat_mul] using rfl
  have hadd_eq : (base + 4 * i).toNat = base.toNat + (4 * i).toNat := by
    apply BitVec.toNat_add
    exact hbase_add_4i_lt
  rw [hadd_eq, h4i_toNat]
  constructor
  · omega
  · have h4i_plus4 : 4 * i.toNat + 4 ≤ 4 * n.toNat := by
      have : 4 * i.toNat < 4 * n.toNat := h4i_lt_4n
      omega
    omega

end GlimmerVerify.Bench
