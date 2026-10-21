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
  have h4i_lt_4n : 4 * i.toNat < 4 * n.toNat := by omega
  have h4i_lt : 4 * i.toNat < 2 ^ 64 := by
    have : 4 * i.toNat < 4 * n.toNat + base.toNat := by omega
    have : 4 * i.toNat < base.toNat + 4 * n.toNat := by omega
    omega
  have hsum_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    have : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := by omega
    omega
  have h4n_lt : 4 * n.toNat < 2 ^ 64 := by
    have : base.toNat + 4 * n.toNat < 2 ^ 64 := hfit
    omega
  have h4i_toNat : (4 * i).toNat = 4 * i.toNat := by
    have h := BitVec.toNat_mul (4 : BitVec 64) i
    simp [BitVec.toNat_ofNat] at h
    rw [h]
    rw [Nat.mod_eq_of_lt h4i_lt]
  have h4n_toNat : (4 * n).toNat = 4 * n.toNat := by
    have h := BitVec.toNat_mul (4 : BitVec 64) n
    simp [BitVec.toNat_ofNat] at h
    rw [h]
    rw [Nat.mod_eq_of_lt h4n_lt]
  have hbase_add_4i : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    have h := BitVec.toNat_add base (4 * i)
    rw [h4i_toNat] at h
    rw [h]
    rw [Nat.mod_eq_of_lt hsum_lt]
  have hbase_add_4n : (base + 4 * n).toNat = base.toNat + 4 * n.toNat := by
    have h := BitVec.toNat_add base (4 * n)
    rw [h4n_toNat] at h
    rw [h]
    have hlt : base.toNat + 4 * n.toNat < 2 ^ 64 := hfit
    rw [Nat.mod_eq_of_lt hlt]
  rw [hbase_add_4i]
  constructor
  · omega
  · omega

end GlimmerVerify.Bench
