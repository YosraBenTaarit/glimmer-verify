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
  have h4n_lt : 4 * n.toNat < 2 ^ 64 := by
    have h0 : 0 ≤ base.toNat := Nat.zero_le _
    omega
  have h4i_lt : 4 * i.toNat < 2 ^ 64 := by
    have : 4 * i.toNat < 4 * n.toNat := by omega
    omega
  have hsum_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    have : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := by omega
    omega
  have h4i_toNat : (4 * i).toNat = 4 * i.toNat := by
    have h1 : (4 * i).toNat = (4.toNat * i.toNat) % 2 ^ 64 := by
      simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [h1]
    exact Nat.mod_eq_of_lt h4i_lt
  have h4n_toNat : (4 * n).toNat = 4 * n.toNat := by
    have h1 : (4 * n).toNat = (4.toNat * n.toNat) % 2 ^ 64 := by
      simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [h1]
    exact Nat.mod_eq_of_lt h4n_lt
  have hadd_i : (base + 4 * i).toNat = (base.toNat + (4 * i).toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_add]
  rw [h4i_toNat] at hadd_i
  have hadd_i_eq : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    rw [hadd_i]
    exact Nat.mod_eq_of_lt hsum_lt
  have hadd_n : (base + 4 * n).toNat = (base.toNat + (4 * n).toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_add]
  rw [h4n_toNat] at hadd_n
  have hadd_n_eq : (base + 4 * n).toNat = base.toNat + 4 * n.toNat := by
    rw [hadd_n]
    exact Nat.mod_eq_of_lt hfit
  constructor
  · rw [hadd_i_eq]
    exact Nat.le_add_left base.toNat _
  · rw [hadd_i_eq]
    have hle : 4 * i.toNat + 4 ≤ 4 * n.toNat := by omega
    omega

end GlimmerVerify.Bench
