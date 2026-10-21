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
  simp [stripedAllocator] at hla hlb ⊢
  by_cases ha : a < R
  · by_cases hb : b < R
    · have hla' : la < blocks := by
        have : (if a < R then blocks else 0) = blocks := by simp [ha]
        omega
      have hlb' : lb < blocks := by
        have : (if b < R then blocks else 0) = blocks := by simp [hb]
        omega
      by_contra h_eq
      have : la * R + a = lb * R + b := h_eq
      have h1 : la * R ≤ la * R + a := Nat.le_add_right _ _
      have h2 : lb * R ≤ lb * R + b := Nat.le_add_right _ _
      omega
    · have : (if b < R then blocks else 0) = 0 := by simp [hb]
      omega
  · have : (if a < R then blocks else 0) = 0 := by simp [ha]
    omega

end GlimmerVerify.Bench
