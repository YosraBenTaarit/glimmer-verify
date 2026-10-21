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
  unfold physSlot at h
  simp only [blockSize] at h
  have hp' : p < A.numBlocks req * 16 := hp
  have hq' : q < A.numBlocks req * 16 := hq
  have h_p : p = p / 16 * 16 + p % 16 := Nat.div_add_mod p 16
  have h_q : q = q / 16 * 16 + q % 16 := Nat.div_add_mod q 16
  have hr1 : p % 16 < 16 := Nat.mod_lt p (by decide)
  have hr2 : q % 16 < 16 := Nat.mod_lt q (by decide)
  have hl1 : p / 16 < A.numBlocks req := by omega
  have hl2 : q / 16 < A.numBlocks req := by omega
  have ht : A.table req (p / 16) = A.table req (q / 16) := by
    have := h
    omega
  have hl : p / 16 = q / 16 := hinj _ _ hl1 hl2 ht
  have hr : p % 16 = q % 16 := by
    have := h
    omega
  rw [hl, hr] at h_p
  rw [h_p] at h_q
  exact h_q.symm

end GlimmerVerify.Bench
