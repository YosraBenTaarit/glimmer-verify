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
  simp only [KVAllocator.Isolated, KVAllocator.table, KVAllocator.numBlocks]
                                                        
  have ha_lt : a < R := by
    by_cases h : a < R
    · exact h
    · simp [h] at hla
      omega
  have hb_lt : b < R := by
    by_cases h : b < R
    · exact h
    · simp [h] at hlb
      omega
  have hla' : la < blocks := by
    simp [ha_lt] at hla
    exact hla
  have hlb' : lb < blocks := by
    simp [hb_lt] at hlb
    exact hlb
  intro heq
                                                         
  have eq : la * R + a = lb * R + b := heq
                                                
  omega

end GlimmerVerify.Bench
