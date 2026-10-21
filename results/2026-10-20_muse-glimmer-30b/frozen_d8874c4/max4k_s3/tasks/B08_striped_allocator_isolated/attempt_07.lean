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
    · simp [h] at hla
      cases hla
  have hb : b < R := by
    by_cases h : b < R
    · exact h
    · simp [h] at hlb
      cases hlb
  simp [ha, hb]
  intro heq
  have hla' : la < blocks := by
    simpa [ha] using hla
  have hlb' : lb < blocks := by
    simpa [hb] using hlb
  have h1 : la * R + a = lb * R + b := heq
  have h2 : a < R := ha
  have h3 : b < R := hb
  have h4 : la < blocks := hla'
  have h5 : lb < blocks := hlb'
  have h6 : la * R ≤ (blocks - 1) * R := Nat.mul_le_mul_right R (Nat.le_of_lt h4)
  have h7 : lb * R ≤ (blocks - 1) * R := Nat.mul_le_mul_right R (Nat.le_of_lt h5)
  have h8 : la * R + a < blocks * R := by
    have : la * R + a ≤ (blocks - 1) * R + (R - 1) := by
      apply Nat.add_le_add
      · exact h6
      · exact Nat.le_trans (Nat.le_of_lt h2) (Nat.sub_le _ _)
    omega
  have h9 : lb * R + b < blocks * R := by
    have : lb * R + b ≤ (blocks - 1) * R + (R - 1) := by
      apply Nat.add_le_add
      · exact h7
      · exact Nat.le_trans (Nat.le_of_lt h3) (Nat.sub_le _ _)
    omega
  omega

end GlimmerVerify.Bench
