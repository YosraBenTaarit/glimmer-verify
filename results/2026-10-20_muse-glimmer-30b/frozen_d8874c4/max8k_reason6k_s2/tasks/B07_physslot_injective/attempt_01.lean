import GlimmerVerify.PagedKVProofs

/-!
B07: no aliasing inside one request.

If a request's page table never maps two of its allocated logical blocks to the same physical
block, then two distinct token positions of that request occupy distinct KV slots, so a decode
step can never overwrite an earlier token of the same conversation.
-/

namespace GlimmerVerify.Bench

open GlimmerVerify

theorem physSlot_injective_within_request (A : KVAllocator) (req p q : Nat)
    (hinj : ∀ l₁ l₂, l₁ < A.numBlocks req → l₂ < A.numBlocks req →
      A.table req l₁ = A.table req l₂ → l₁ = l₂)
    (hp : A.Owns req p) (hq : A.Owns req q)
    (h : physSlot A.table req p = physSlot A.table req q) : p = q := by
  unfold KVAllocator.Owns blockSize at hp hq
  unfold physSlot blockSize at h
  have hp_lt : p < A.numBlocks req * 16 := hp
  have hq_lt : q < A.numBlocks req * 16 := hq
  set b1 := p / 16
  set r1 := p % 16
  set b2 := q / 16
  set r2 := q % 16
  have hdiv1 : p = b1 * 16 + r1 := (Nat.div_add_mod p 16).symm
  have hmod1 : r1 < 16 := Nat.mod_lt p (by decide)
  have hdiv2 : q = b2 * 16 + r2 := (Nat.div_add_mod q 16).symm
  have hmod2 : r2 < 16 := Nat.mod_lt q (by decide)
  have hb1 : b1 < A.numBlocks req := by omega
  have hb2 : b2 < A.numBlocks req := by omega
  rw [hdiv1, hdiv2] at h
  have h_eq : A.table req b1 * 16 + r1 = A.table req b2 * 16 + r2 := by
    simpa [hdiv1, hdiv2] using h
  have h_mod : r1 = r2 := by
    have := Nat.add_mul_mod_self_right (A.table req b1) 16 r1
    have := Nat.add_mul_mod_self_right (A.table req b2) 16 r2
                                            
    have h1 : (A.table req b1 * 16 + r1) % 16 = r1 := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_add]
    have h2 : (A.table req b2 * 16 + r2) % 16 = r2 := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_add]
    have : (A.table req b1 * 16 + r1) % 16 = (A.table req b2 * 16 + r2) % 16 := by
      rw [h_eq]
    omega
  have h_tbl : A.table req b1 = A.table req b2 := by
    have : A.table req b1 * 16 = A.table req b2 * 16 := by omega
    exact Nat.mul_left_inj (by decide) ▸ this
  have hb_eq : b1 = b2 := hinj b1 b2 hb1 hb2 h_tbl
  rw [hb_eq, h_mod]
  exact (Nat.div_add_mod p 16).symm

end GlimmerVerify.Bench
