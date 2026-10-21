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
  unfold physSlot KVAllocator.Owns blockSize at *
  have hb1 : p / 16 < A.numBlocks req := by omega
  have hb2 : q / 16 < A.numBlocks req := by omega
  have h_eq : A.table req (p / 16) * 16 + p % 16 = A.table req (q / 16) * 16 + q % 16 := h
  have h_r_eq : p % 16 = q % 16 := by omega
  have h_t_eq : A.table req (p / 16) = A.table req (q / 16) := by omega
  have h_b_eq : p / 16 = q / 16 := hinj (p / 16) (q / 16) hb1 hb2 h_t_eq
  have h_p : p = 16 * (p / 16) + p % 16 := (Nat.div_add_mod p 16).symm
  have h_q : q = 16 * (q / 16) + q % 16 := (Nat.div_add_mod q 16).symm
  rw [h_b_eq, h_r_eq] at h_eq
  rw [h_p, h_q] at h_eq
  exact h_eq

end GlimmerVerify.Bench
