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
  have hi : i.toNat < n.toNat := BitVec.toNat_lt_toNat hp1
  have h4i_lt : 4 * i.toNat < 4 * n.toNat := by omega
  have hsum_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    have : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := by omega
    omega
  have hbase_add_4i_toNat : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    have h1 : (base + 4 * i).toNat = (base.toNat + (4 * i).toNat) % 2 ^ 64 := by
      simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have h2 : (4 * i).toNat = 4 * i.toNat := by
      simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [h2] at h1
    rw [Nat.mod_eq_of_lt hsum_lt] at h1
    exact h1
  have hbase_add_4n_toNat : (base + 4 * n).toNat = base.toNat + 4 * n.toNat := by
    have h1 : (base + 4 * n).toNat = (base.toNat + (4 * n).toNat) % 2 ^ 64 := by
      simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have h2 : (4 * n).toNat = 4 * n.toNat := by
      simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [h2] at h1
    have hlt : base.toNat + 4 * n.toNat < 2 ^ 64 := hfit
    rw [Nat.mod_eq_of_lt hlt] at h1
    exact h1
  rw [hbase_add_4i_toNat]
  constructor
  · omega
  · omega

end GlimmerVerify.Bench
