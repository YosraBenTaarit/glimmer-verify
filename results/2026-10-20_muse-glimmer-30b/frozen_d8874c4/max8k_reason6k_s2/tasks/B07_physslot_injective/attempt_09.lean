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
  have b1_lt : p / 16 < A.numBlocks req := by omega
  have b2_lt : q / 16 < A.numBlocks req := by omega
  have hmod_left : (A.table req (p / 16) * 16 + p % 16) % 16 = p % 16 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_add]
  have hmod_right : (A.table req (q / 16) * 16 + q % 16) % 16 = q % 16 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_add]
  have hmod_eq : p % 16 = q % 16 := by
    have := congrArg (· % 16) h
    rw [hmod_left, hmod_right] at this
    exact this
  have htbl_eq : A.table req (p / 16) * 16 = A.table req (q / 16) * 16 := by
    have := h
    omega
  have htbl : A.table req (p / 16) = A.table req (q / 16) := by
    have h16_ne : (16 : Nat) ≠ 0 := by decide
    exact (Nat.mul_right_inj h16_ne).mp htbl_eq
  have hb_eq : p / 16 = q / 16 := hinj (p / 16) (q / 16) b1_lt b2_lt htbl
  have hdiv_p : 16 * (p / 16) + p % 16 = p := Nat.div_add_mod p 16
  have hdiv_q : 16 * (q / 16) + q % 16 = q := Nat.div_add_mod q 16
  rw [hb_eq, hmod_eq] at hdiv_p
  omega

end GlimmerVerify.Bench
