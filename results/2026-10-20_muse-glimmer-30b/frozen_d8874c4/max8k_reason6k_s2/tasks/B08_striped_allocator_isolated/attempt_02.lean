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
    ·                            
      have hnum_a : (if a < R then blocks else 0) = blocks := by simp [ha]
      have hnum_b : (if b < R then blocks else 0) = blocks := by simp [hb]
      rw [hnum_a] at hla
      rw [hnum_b] at hlb
      by_contra h_eq
      have : la * R + a = lb * R + b := by
        simp [h_eq]
      omega
    ·              
      have hnum_b : (if b < R then blocks else 0) = 0 := by simp [hb]
      rw [hnum_b] at hlb
      omega
  ·              
    have hnum_a : (if a < R then blocks else 0) = 0 := by simp [ha]
    rw [hnum_a] at hla
    omega

end GlimmerVerify.Bench
