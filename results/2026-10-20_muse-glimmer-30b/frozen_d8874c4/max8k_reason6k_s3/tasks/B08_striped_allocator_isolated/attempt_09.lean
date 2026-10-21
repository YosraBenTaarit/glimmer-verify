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
  by_cases ha : a < R
  · by_cases hb : b < R
    · have hla' : la < blocks := by
        cases h : (if a < R then blocks else 0) <;> simp [h, ha] at hla ⊢
      have hlb' : lb < blocks := by
        cases h : (if b < R then blocks else 0) <;> simp [h, hb] at hlb ⊢
      intro heq
      have hmod_a : (la * R + a) % R = a := by
        rw [Nat.add_mod]
        rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      have hmod_b : (lb * R + b) % R = b := by
        rw [Nat.add_mod]
        rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      have : a = b := by
        rw [← hmod_a, ← hmod_b]
        rw [heq]
      contradiction
    · cases h : (if b < R then blocks else 0) <;> simp [h, hb] at hlb
  · cases h : (if a < R then blocks else 0) <;> simp [h, ha] at hla

end GlimmerVerify.Bench
