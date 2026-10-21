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
    exact (BitVec.lt_iff_toNat_lt).mp hp1
  have h4i_le : 4 * i.toNat ≤ 4 * n.toNat := by omega
  have hsum_le : base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := by omega
  have hsum_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    calc
      base.toNat + 4 * i.toNat ≤ base.toNat + 4 * n.toNat := hsum_le
      _ < 2 ^ 64 := hfit
  have h4i_lt : 4 * i.toNat < 2 ^ 64 := by omega
  have h_add_toNat : (base + (4 : BitVec 64) * i).toNat = (base.toNat + 4 * i.toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h_eq : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    rw [h_add_toNat]
    have : base.toNat + 4 * i.toNat < 2 ^ 64 := hsum_lt
    omega
  rw [h_eq]
  constructor
  · omega
  · have : base.toNat + 4 * i.toNat + 4 ≤ base.toNat + 4 * n.toNat := by
      have : 4 * i.toNat + 4 ≤ 4 * n.toNat := by omega
      omega
    omega

end GlimmerVerify.Bench
