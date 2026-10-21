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
          unfold stripedAllocator
          simp [ha]
        rw [this] at hla
        exact hla
      have hlb' : lb < blocks := by
        have : (stripedAllocator R blocks).numBlocks b = blocks := by
          unfold stripedAllocator
          simp [hb]
        rw [this] at hlb
        exact hlb
      have h_eq : la * R + a = lb * R + b → False := by
        intro heq
        have h1 : la * R ≤ la * R + a := Nat.le_add_right _ _
        have h2 : lb * R ≤ lb * R + b := Nat.le_add_right _ _
        omega
      exact h_eq
    · have hnum_b : (stripedAllocator R blocks).numBlocks b = 0 := by
        unfold stripedAllocator
        simp [hb]
      rw [hnum_b] at hlb
      omega
  · have hnum_a : (stripedAllocator R blocks).numBlocks a = 0 := by
      unfold stripedAllocator
      simp [ha]
    rw [hnum_a] at hla
    omega

end GlimmerVerify.Bench
