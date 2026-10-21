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
  intro a b hab la lb hla hlb h_eq
  simp [stripedAllocator] at hla hlb h_eq
  have ha : a < R := by
    by_cases h : a < R
    · exact h
    · simp [h] at hla
      omega
  have hb : b < R := by
    by_cases h : b < R
    · exact h
    · simp [h] at hlb
      omega
  have hmod_a : (la * R + a) % R = a := by
    rw [Nat.add_comm a (la * R)]
    rw [Nat.add_mul_mod_self_right a R la]
    rw [Nat.mod_eq_of_lt ha]
  have hmod_b : (lb * R + b) % R = b := by
    rw [Nat.add_comm b (lb * R)]
    rw [Nat.add_mul_mod_self_right b R lb]
    rw [Nat.mod_eq_of_lt hb]
  have : a = b := by
    have : (la * R + a) % R = (lb * R + b) % R := by rw [h_eq]
    rw [hmod_a, hmod_b] at this
    exact this
  contradiction

end GlimmerVerify.Bench
