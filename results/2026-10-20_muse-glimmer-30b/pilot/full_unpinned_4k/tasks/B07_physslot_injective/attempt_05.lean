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
  simp [blockSize] at hp hq h
  have hdiv1 : p / 16 < A.numBlocks req := by omega
  have hdiv2 : q / 16 < A.numBlocks req := by omega
  have hmod_lt1 : p % 16 < 16 := Nat.mod_lt p (by decide)
  have hmod_lt2 : q % 16 < 16 := Nat.mod_lt q (by decide)
  have h_mod : p % 16 = q % 16 := by
    have : (A.table req (p / 16) * 16 + p % 16) % 16 =
           (A.table req (q / 16) * 16 + q % 16) % 16 := by rw [h]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_self] at this
    omega
  have h_table : A.table req (p / 16) = A.table req (q / 16) := by
    have : A.table req (p / 16) * 16 + p % 16 = A.table req (q / 16) * 16 + q % 16 := h
    rw [h_mod] at this
    omega
  have h_l : p / 16 = q / 16 := hinj _ _ hdiv1 hdiv2 h_table
  have p_eq' : 16 * (p / 16) + p % 16 = p := Nat.div_add_mod p 16
  have q_eq' : 16 * (q / 16) + q % 16 = q := Nat.div_add_mod q 16
  have : 16 * (p / 16) + p % 16 = 16 * (q / 16) + q % 16 := by
    rw [h_l, h_mod]
  rw [←p_eq', ←q_eq'] at this
  exact this.symm

end GlimmerVerify.Bench
