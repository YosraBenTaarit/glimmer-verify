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
  have hpblk : p / 16 < A.numBlocks req := by omega
  have hqblk : q / 16 < A.numBlocks req := by omega
  have hp_eq : p = 16 * (p / 16) + p % 16 := by
    rw [← Nat.div_add_mod p 16]
  have hq_eq : q = 16 * (q / 16) + q % 16 := by
    rw [← Nat.div_add_mod q 16]
  have h_eq : A.table req (p / 16) * 16 + p % 16 = A.table req (q / 16) * 16 + q % 16 := h
  have h_t_eq : A.table req (p / 16) = A.table req (q / 16) := by
    have h1 : A.table req (p / 16) * 16 ≤ A.table req (p / 16) * 16 + p % 16 := Nat.le_add_right _ _
    have h2 : A.table req (p / 16) * 16 + p % 16 < A.table req (p / 16) * 16 + 16 := by omega
    have h3 : A.table req (q / 16) * 16 ≤ A.table req (q / 16) * 16 + q % 16 := Nat.le_add_right _ _
    have h4 : A.table req (q / 16) * 16 + q % 16 < A.table req (q / 16) * 16 + 16 := by omega
    have hle1 : A.table req (p / 16) * 16 ≤ A.table req (q / 16) * 16 + q % 16 := by
      rw [← h_eq]; exact h1
    have hle2 : A.table req (q / 16) * 16 ≤ A.table req (p / 16) * 16 + p % 16 := by
      rw [h_eq]; exact h3
    omega
  have h_r_eq : p % 16 = q % 16 := by
    have : A.table req (p / 16) * 16 + p % 16 = A.table req (p / 16) * 16 + q % 16 := by
      rw [h_t_eq] at h_eq
      rw [h_eq]
    omega
  have hb_eq : p / 16 = q / 16 := hinj (p / 16) (q / 16) hpblk hqblk h_t_eq
  rw [hb_eq, h_r_eq] at hp_eq
  rw [hp_eq, hq_eq]
  omega

end GlimmerVerify.Bench
