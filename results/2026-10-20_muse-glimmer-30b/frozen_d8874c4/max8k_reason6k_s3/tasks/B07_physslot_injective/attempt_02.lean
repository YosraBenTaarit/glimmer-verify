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
  have hmodp : p % 16 < 16 := Nat.mod_lt p (by decide)
  have hmodq : q % 16 < 16 := Nat.mod_lt q (by decide)
  have hdivp : p = 16 * (p / 16) + p % 16 := Nat.div_add_mod p 16
  have hdivq : q = 16 * (q / 16) + q % 16 := Nat.div_add_mod q 16
  have hpblk : p / 16 < A.numBlocks req := by omega
  have hqblk : q / 16 < A.numBlocks req := by omega
  let b1 := p / 16
  let b2 := q / 16
  let r1 := p % 16
  let r2 := q % 16
  have ht : A.table req b1 * 16 + r1 = A.table req b2 * 16 + r2 := by
    simpa [b1, b2, r1, r2, Nat.mul_comm] using h
  have h_t_eq : A.table req b1 = A.table req b2 := by
    have h1 : A.table req b1 * 16 ≤ A.table req b1 * 16 + r1 := Nat.le_add_right _ _
    have h2 : A.table req b1 * 16 + r1 < A.table req b1 * 16 + 16 := by omega
    have h3 : A.table req b2 * 16 ≤ A.table req b2 * 16 + r2 := Nat.le_add_right _ _
    have h4 : A.table req b2 * 16 + r2 < A.table req b2 * 16 + 16 := by omega
    have hle1 : A.table req b1 * 16 ≤ A.table req b2 * 16 + r2 := by
      rw [← ht]; exact h1
    have hle2 : A.table req b2 * 16 ≤ A.table req b1 * 16 + r1 := by
      rw [ht]; exact h3
    omega
  have h_r_eq : r1 = r2 := by
    have : A.table req b1 * 16 + r1 = A.table req b1 * 16 + r2 := by
      rw [h_t_eq] at ht; exact ht
    omega
  have hb_eq : b1 = b2 := hinj b1 b2 hpblk hqblk h_t_eq
  subst hb_eq
  subst h_r_eq
  rw [hdivp, hdivq]
  omega

end GlimmerVerify.Bench
