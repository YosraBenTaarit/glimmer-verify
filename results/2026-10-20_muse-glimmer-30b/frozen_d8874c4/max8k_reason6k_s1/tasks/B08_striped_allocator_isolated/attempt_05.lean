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
                                                       
  have ha_lt : a < R := by
    by_cases h : a < R
    · exact h
    · have hnum : (if a < R then blocks else 0) = 0 := by
        simp [h]
      rw [hnum] at hla
      omega
  have hb_lt : b < R := by
    by_cases h : b < R
    · exact h
    · have hnum : (if b < R then blocks else 0) = 0 := by
        simp [h]
      rw [hnum] at hlb
      omega
                                        
  simp [ha_lt, hb_lt]
  intro heq
                               
  have h_eq : la * R + a = lb * R + b := heq
                       
  have hmod_a : a % R = a := Nat.mod_eq_of_lt ha_lt
  have hmod_b : b % R = b := Nat.mod_eq_of_lt hb_lt
  have hmod_la : (la * R) % R = 0 := by
    simp [Nat.mul_mod, Nat.mod_self]
  have hmod_lb : (lb * R) % R = 0 := by
    simp [Nat.mul_mod, Nat.mod_self]
  have h1 : (la * R + a) % R = a := by
    simp [Nat.add_mod, hmod_la, hmod_a]
  have h2 : (lb * R + b) % R = b := by
    simp [Nat.add_mod, hmod_lb, hmod_b]
  have h3 : (la * R + a) % R = (lb * R + b) % R := by
    rw [h_eq]
  rw [h1, h2] at h3
                                  
  have : a = b := by omega
  contradiction

end GlimmerVerify.Bench
