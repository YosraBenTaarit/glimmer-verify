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
  have hp_div : 16 * (p / 16) + p % 16 = p := Nat.div_add_mod p 16
  have hq_div : 16 * (q / 16) + q % 16 = q := Nat.div_add_mod q 16
  let a := A.table req (p / 16)
  let b := A.table req (q / 16)
  let r1 := p % 16
  let r2 := q % 16
  have h_eq : a * 16 + r1 = b * 16 + r2 := by
    simpa [a, b, r1, r2, Nat.mul_comm] using h
  have h_a_eq_b : a = b := by
    have h1 : a * 16 ≤ a * 16 + r1 := Nat.le_add_right _ _
    have h2 : a * 16 + r1 < a * 16 + 16 := by omega
    have h3 : b * 16 ≤ b * 16 + r2 := Nat.le_add_right _ _
    have h4 : b * 16 + r2 < b * 16 + 16 := by omega
    have hle1 : a * 16 ≤ b * 16 + r2 := by rw [← h_eq]; exact h1
    have hle2 : b * 16 ≤ a * 16 + r1 := by rw [h_eq]; exact h3
    omega
  have h_r_eq : r1 = r2 := by
    rw [h_a_eq_b] at h_eq
    omega
  have h_b_eq : p / 16 = q / 16 := hinj (p / 16) (q / 16) hpblk hqblk h_a_eq_b
  rw [h_b_eq, h_r_eq]
  rw [← hp_div, ← hq_div]
  omega

end GlimmerVerify.Bench
