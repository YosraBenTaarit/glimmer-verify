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
  simp [KVAllocator.Isolated]
                                                       
  have ha_lt : a < R := by
    by_cases h : a < R
    · exact h
    · have : (if a < R then blocks else 0) = 0 := by simp [h]
      rw [this] at hla
      omega
  have hb_lt : b < R := by
    by_cases h : b < R
    · exact h
    · have : (if b < R then blocks else 0) = 0 := by simp [h]
      rw [this] at hlb
      omega
                                 
  simp [ha_lt, hb_lt]
  intro heq
  have h1 : la * R + a = lb * R + b := heq
                            
  have hab_abs : a - b ≠ 0 := by
    intro h0
    apply hab
    omega
                
  have hlt : b - a < R := by omega
  have hlt' : a - b < R := by omega
                                       
  have hdiff : la * R - lb * R = b - a := by omega
  have hmul : (la - lb) * R = b - a := by omega
                                                                     
  by_cases hle : la ≥ lb
  · have hpos : 0 < la - lb := by omega
    have hRpos : 0 < (la - lb) * R := by omega
    have : 0 < b - a := by omega
    omega
  · have hneg : lb > la := by omega
    have hpos : 0 < lb - la := by omega
    have hRpos : 0 < (lb - la) * R := by omega
    have : a - b > 0 := by omega
    omega

end GlimmerVerify.Bench
