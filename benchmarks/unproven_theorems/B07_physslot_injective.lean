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
  sorry

end GlimmerVerify.Bench
