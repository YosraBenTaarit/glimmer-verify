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
  have hi : i.toNat < n.toNat := BitVec.ult_iff_toNat_lt.mp hp1
  have hmul : (4 * i).toNat = 4 * i.toNat := by
    have := BitVec.toNat_mul (4 : BitVec 64) i
    simp [BitVec.ofNat_eq] at this
    exact this
  have hadd : (base + 4 * i).toNat = base.toNat + 4 * i.toNat := by
    have h1 : (base + 4 * i).toNat = (base.toNat + (4 * i).toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_add]
    rw [h1, hmul]
    have hlt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
      have h1 : 4 * i.toNat ≤ 4 * n.toNat := by omega
      omega
    rw [Nat.add_mod_of_lt hlt]
  have hle : base.toNat ≤ base.toNat + 4 * i.toNat := by omega
  have hle2 : base.toNat + 4 * i.toNat + 4 ≤ base.toNat + 4 * n.toNat := by omega
  constructor
  · rw [hadd]; exact hle
  · rw [hadd]; exact hle2

end GlimmerVerify.Bench
