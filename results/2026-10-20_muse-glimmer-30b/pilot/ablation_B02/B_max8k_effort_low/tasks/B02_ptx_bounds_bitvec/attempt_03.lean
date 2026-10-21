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
  have hi : i.toNat < n.toNat := by
    have h := BitVec.toNat_lt_toNat hp1
    exact h
  have h4i_lt_4n : 4 * i.toNat < 4 * n.toNat := by omega
  have h4i_lt : 4 * i.toNat < 2 ^ 64 := by
    have : 4 * i.toNat < base.toNat + 4 * n.toNat := by omega
    omega
  have hsum_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    have : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := by omega
    omega
  have h4n_lt : 4 * n.toNat < 2 ^ 64 := by
    have : base.toNat + 4 * n.toNat < 2 ^ 64 := hfit
    omega
  have h4i_toNat : (4 * i).toNat = 4 * i.toNat := by
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h4i_lt]
  have h4n_toNat : (4 * n).toNat = 4 * n.toNat := by
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h4n_lt]
  have hbase_add_4i : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    simp [BitVec.toNat_add]
    rw [h4i_toNat]
    rw [Nat.mod_eq_of_lt hsum_lt]
  have hbase_add_4n : (base + 4 * n).toNat = base.toNat + 4 * n.toNat := by
    simp [BitVec.toNat_add]
    rw [h4n_toNat]
    have hlt : base.toNat + 4 * n.toNat < 2 ^ 64 := hfit
    rw [Nat.mod_eq_of_lt hlt]
  rw [hbase_add_4i]
  constructor
  · omega
  · omega

end GlimmerVerify.Bench
