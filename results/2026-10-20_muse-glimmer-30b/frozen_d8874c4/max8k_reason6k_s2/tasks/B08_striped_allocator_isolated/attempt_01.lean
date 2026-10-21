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
  unfold stripedAllocator at *
  simp [KVAllocator.Isolated]
  unfold stripedAllocator
  simp only
  split_ifs with h_a h_b
  ·                        
    have ha_lt : a < R := h_a
    have hb_lt : b < R := h_b
    have hla' : la < blocks := by
      have : (if a < R then blocks else 0) = blocks := by simp [h_a]
      rw [this] at hla
      exact hla
    have hlb' : lb < blocks := by
      have : (if b < R then blocks else 0) = blocks := by simp [h_b]
      rw [this] at hlb
      exact hlb
    by_contra h_eq
    have eq : la * R + a = lb * R + b := by
      simp [h_eq]
    omega
  ·                
    have : (if b < R then blocks else 0) = 0 := by simp [h_b]
    rw [this] at hlb
    omega
  ·                
    have : (if a < R then blocks else 0) = 0 := by simp [h_a]
    rw [this] at hla
    omega
  ·            
    have ha0 : (if a < R then blocks else 0) = 0 := by simp [h_a]
    have hb0 : (if b < R then blocks else 0) = 0 := by simp [h_b]
    rw [ha0] at hla
    rw [hb0] at hlb
    omega

end GlimmerVerify.Bench
