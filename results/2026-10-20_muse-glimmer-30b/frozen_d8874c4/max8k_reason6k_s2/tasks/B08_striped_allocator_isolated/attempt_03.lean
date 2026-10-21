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
  unfold stripedAllocator
  simp only
  by_cases ha : a < R
  · by_cases hb : b < R
    ·               
      have hla' : la < blocks := by
        simp [ha] at hla
        exact hla
      have hlb' : lb < blocks := by
        simp [hb] at hlb
        exact hlb
      by_contra h_eq
      have : la * R + a = lb * R + b := by
        rw [h_eq]
      omega
    ·              
      have hlb0 : lb < 0 := by
        simp [hb] at hlb
      omega
  ·              
    have hla0 : la < 0 := by
      simp [ha] at hla
    omega

end GlimmerVerify.Bench
