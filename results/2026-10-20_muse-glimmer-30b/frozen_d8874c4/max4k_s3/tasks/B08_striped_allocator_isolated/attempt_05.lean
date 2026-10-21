import GlimmerVerify.PagedKVProofs

/-!
B08: the isolation hypothesis is satisfiable by a real allocator.

The striped allocator for `R` concurrent requests gives request `r < R` the physical blocks
`r, r + R, r + 2R, ...` and gives requests `r ≥ R` nothing. Prove it is `Isolated`, so
`paged_kv_isolation` applies to it non-vacuously.
-/

namespace GlimmerVerify.Bench

open GlimmerVerify

def stripedAllocator (R blocks : Nat) : KVAllocator where
  table r l := l * R + r
  numBlocks r := if r < R then blocks else 0

theorem stripedAllocator_isolated (R blocks : Nat) : (stripedAllocator R blocks).Isolated := by
  intro a b hab la lb hla hlb
  unfold stripedAllocator
  have ha : a < R := by
    by_cases h : a < R
    · exact h
    · simp [h] at hla; omega
  have hb : b < R := by
    by_cases h : b < R
    · exact h
    · simp [h] at hlb; omega
  simp [ha, hb]
  intro heq
  have h1 : la * R + a = lb * R + b := heq
  have h2 : a ≠ b := hab
  have h3 : la < blocks := by
    simp [ha] at hla; exact hla
  have h4 : lb < blocks := by
    simp [hb] at hlb; exact hlb
  have h5 : a < R := ha
  have h6 : b < R := hb
  have h7 : la * R < blocks * R := Nat.mul_lt_mul_right R h3
  have h8 : lb * R < blocks * R := Nat.mul_lt_mul_right R h4
  have h9 : la * R + a < blocks * R + R := by
    have : la * R + a < blocks * R + R := by
      have : la * R + a ≤ la * R + (R - 1) + 1 := by
        apply Nat.add_le_add_left
        exact Nat.add_le_add_right (Nat.mul_le_mul_right R (Nat.le_of_lt h5)) (Nat.zero_le _)
      omega
    exact this
  have h10 : lb * R + b < blocks * R + R := by
    have : lb * R + b ≤ lb * R + (R - 1) + 1 := by
      apply Nat.add_le_add_left
      exact Nat.add_le_add_right (Nat.mul_le_mul_right R (Nat.le_of_lt h6)) (Nat.zero_le _)
      omega
    exact this
  omega

end GlimmerVerify.Bench
