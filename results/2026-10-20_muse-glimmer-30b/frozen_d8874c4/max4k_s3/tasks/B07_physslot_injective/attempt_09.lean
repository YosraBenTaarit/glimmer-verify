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
  simp [blockSize] at hp hq
  unfold physSlot blockSize at h
  have hr1 : p % 16 < 16 := Nat.mod_lt p (by decide)
  have hr2 : q % 16 < 16 := Nat.mod_lt q (by decide)
  have hb1 : p / 16 < A.numBlocks req := by omega
  have hb2 : q / 16 < A.numBlocks req := by omega
  have h_t_eq : A.table req (p / 16) = A.table req (q / 16) := by omega
  have h_b_eq : p / 16 = q / 16 := hinj (p / 16) (q / 16) hb1 hb2 h_t_eq
  have h_r_eq : p % 16 = q % 16 := by omega
  have hdiv1 : 16 * (p / 16) + p % 16 = p := Nat.div_add_mod p 16
  have hdiv2 : 16 * (q / 16) + q % 16 = q := Nat.div_add_mod q 16
  omega

end GlimmerVerify.Bench
