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
  simp only [KVAllocator.Isolated]
  by_cases ha : a < R
  · by_cases hb : b < R
    · have hla' : la < blocks := by
        have : (stripedAllocator R blocks).numBlocks a = blocks := by
          unfold stripedAllocator; simp [ha]
        rw [this] at hla; exact hla
      have hlb' : lb < blocks := by
        have : (stripedAllocator R blocks).numBlocks b = blocks := by
          unfold stripedAllocator; simp [hb]
        rw [this] at hlb; exact hlb
      intro heq
      by_cases hla_eq : la = lb
      · rw [hla_eq] at heq
        omega
      · by_cases hla_lt : la < lb
        · have hle : la + 1 ≤ lb := Nat.succ_le_of_lt hla_lt
          have haR : a < R := ha
          have hbR : b < R := hb
          have h1 : la * R + a ≤ la * R + (R - 1) := Nat.le_add_right _ _
                                
          have h2 : la * R + R ≤ lb * R := by
            have : la + 1 ≤ lb := hle
            exact Nat.mul_le_mul_right R this
          omega
        · have hlb_lt : lb < la := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hla_lt) (Ne.symm hla_eq)
          have hle : lb + 1 ≤ la := Nat.succ_le_of_lt hlb_lt
          have haR : a < R := ha
          have hbR : b < R := hb
          have h2 : lb * R + R ≤ la * R := by
            have : lb + 1 ≤ la := hle
            exact Nat.mul_le_mul_right R this
          omega
    · have hnum_b : (stripedAllocator R blocks).numBlocks b = 0 := by
        unfold stripedAllocator; simp [hb]
      rw [hnum_b] at hlb
      omega
  · have hnum_a : (stripedAllocator R blocks).numBlocks a = 0 := by
      unfold stripedAllocator; simp [ha]
    rw [hnum_a] at hla
    omega

end GlimmerVerify.Bench
