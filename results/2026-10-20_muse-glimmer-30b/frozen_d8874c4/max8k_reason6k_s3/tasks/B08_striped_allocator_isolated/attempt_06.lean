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
    · simp [ha, hb] at hla hlb
      intro heq
      have hmod_a : (la * R + a) % R = a := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      have hmod_b : (lb * R + b) % R = b := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      have : a = b := by
        have h1 : (la * R + a) % R = (lb * R + b) % R := by rw [heq]
        rw [hmod_a, hmod_b] at h1
        exact h1
      contradiction
    · simp [ha, hb] at hlb
      omega
  · simp [ha] at hla
    omega

end GlimmerVerify.Bench
