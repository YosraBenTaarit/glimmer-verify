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
    have h : i < n := hp1
    exact h
  have h4pos : 0 < 4 := by decide
  have h4i_lt_4n : 4 * i.toNat < 4 * n.toNat := Nat.mul_lt_mul_of_pos_left hi h4pos
                                                                   
  have hbase_add_4i_lt : base.toNat + 4 * i.toNat < 2 ^ 64 := by
    omega
  have h4i_lt_pow : 4 * i.toNat < 2 ^ 64 := by
    omega
                                 
  have h4i_toNat : (4 * i).toNat = 4 * i.toNat := by
    rw [BitVec.toNat_mul]
    simp [Nat.mod_eq_of_lt h4i_lt_pow]
                           
  have hsum_toNat : (base + 4 * i).toNat = base.toNat + (4 * i).toNat := by
    rw [BitVec.toNat_add]
    simp [Nat.mod_eq_of_lt hbase_add_4i_lt]
  rw [hsum_toNat, h4i_toNat]
  constructor
  · omega
  · have h4i_plus4_le : 4 * i.toNat + 4 ≤ 4 * n.toNat := by omega [h4i_lt_4n]
    omega [h4i_plus4_le]

end GlimmerVerify.Bench
