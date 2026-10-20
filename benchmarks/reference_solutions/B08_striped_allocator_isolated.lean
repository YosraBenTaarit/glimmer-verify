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
  intro a b hab la lb hla hlb heq
  simp only [stripedAllocator] at hla hlb heq
  have ha : a < R := by
    by_cases h : a < R
    · exact h
    · simp [h] at hla
  have hb : b < R := by
    by_cases h : b < R
    · exact h
    · simp [h] at hlb
  have key : ∀ l r, r < R → (l * R + r) % R = r := by
    intro l r hr
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  exact hab (by rw [← key la a ha, ← key lb b hb, heq])

end GlimmerVerify.Bench
