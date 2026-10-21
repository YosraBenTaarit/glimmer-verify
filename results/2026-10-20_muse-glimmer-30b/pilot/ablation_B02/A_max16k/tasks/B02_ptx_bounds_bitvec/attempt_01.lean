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
  have h4i_lt : 4 * i.toNat < 2 ^ 64 := by
    have h1 : 4 * i.toNat < 4 * n.toNat := by omega
    have h2 : 4 * n.toNat < 2 ^ 64 := by omega
    omega
  have hsum_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    have : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := by omega
    omega
  have h4i_toNat : (4 * i).toNat = 4 * i.toNat := by
    rw [BitVec.toNat_mul]
    rw [BitVec.toNat_ofNat]
    simp [Nat.mod_eq_of_lt h4i_lt]
  have hsum_toNat : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    rw [BitVec.toNat_add]
    rw [h4i_toNat]
    rw [Nat.mod_eq_of_lt hsum_lt]
  constructor
  · rw [hsum_toNat]
    omega
  · rw [hsum_toNat]
    omega

end GlimmerVerify.Bench
