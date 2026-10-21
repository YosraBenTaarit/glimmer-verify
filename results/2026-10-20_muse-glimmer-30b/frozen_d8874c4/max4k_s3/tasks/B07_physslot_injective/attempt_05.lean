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
  unfold KVAllocator.Owns at hp hq
  unfold physSlot blockSize
  set b1 := p / 16
  set r1 := p % 16
  set b2 := q / 16
  set r2 := q % 16
  have hdiv1 : p = b1 * 16 + r1 := Nat.div_add_mod p 16
  have hdiv2 : q = b2 * 16 + r2 := Nat.div_add_mod q 16
  have hr1_lt : r1 < 16 := Nat.mod_lt (by decide)
  have hr2_lt : r2 < 16 := Nat.mod_lt (by decide)
  have hb1 : b1 < A.numBlocks req := by omega
  have hb2 : b2 < A.numBlocks req := by omega
  have h_eq : A.table req b1 * 16 + r1 = A.table req b2 * 16 + r2 := h
  have h_t_eq : A.table req b1 = A.table req b2 := by omega
  have h_b_eq : b1 = b2 := hinj b1 b2 hb1 hb2 h_t_eq
  have h_r_eq : r1 = r2 := by omega
  omega

end GlimmerVerify.Bench
