import GlimmerVerify.PagedKVProofs

/-!
B06: byte-level cross-tenant isolation.

Each KV slot holds a row of `rowBytes` bytes, and byte `e < rowBytes` of slot `s` lives at
`s * rowBytes + e`. Lifting `GlimmerVerify.paged_kv_isolation` from slots to bytes: two different
requests never touch the same byte of the KV pool, whatever the (non-literal) row width.
-/

namespace GlimmerVerify.Bench

open GlimmerVerify

theorem paged_kv_isolation_bytes (A : KVAllocator) (hiso : A.Isolated) {a b pa pb ea eb rowBytes : Nat}
    (hab : a ≠ b) (ha : A.Owns a pa) (hb : A.Owns b pb) (hea : ea < rowBytes) (heb : eb < rowBytes) :
    physSlot A.table a pa * rowBytes + ea ≠ physSlot A.table b pb * rowBytes + eb := by
  have hslot_ne : physSlot A.table a pa ≠ physSlot A.table b pb :=
    paged_kv_isolation A hiso hab ha hb
  intro h_eq
  let s1 := physSlot A.table a pa
  let s2 := physSlot A.table b pb
  have h1_low : s1 * rowBytes ≤ s1 * rowBytes + ea := Nat.le_add_right _ _
  have h1_high : s1 * rowBytes + ea < s1 * rowBytes + rowBytes := Nat.add_lt_add_left hea _
  have h2_low : s2 * rowBytes ≤ s2 * rowBytes + eb := Nat.le_add_right _ _
  have h2_high : s2 * rowBytes + eb < s2 * rowBytes + rowBytes := Nat.add_lt_add_left heb _
  have hrow_pos : 0 < rowBytes := Nat.zero_lt_of_lt hea
  by_cases h_eq_s : s1 = s2
  · subst h_eq_s
    have : ea = eb := by omega
    subst this
    exact hslot_ne rfl
  · have hne : s1 ≠ s2 := h_eq_s
    have hlt_or_gt : s1 < s2 ∨ s2 < s1 := Nat.lt_or_gt_of_ne hne
    cases hlt_or_gt with
    | inl hlt =>
        have h_ge : s1 * rowBytes + rowBytes ≤ s2 * rowBytes := by
          have : s1 + 1 ≤ s2 := Nat.succ_le_of_lt hlt
          have : (s1 + 1) * rowBytes ≤ s2 * rowBytes := Nat.mul_le_mul_right _ this
          simpa [Nat.add_mul] using this
        have hlt1 : s1 * rowBytes + ea < s2 * rowBytes := by
          exact Nat.lt_of_lt_of_le h1_high h_ge
        have h_eq1 : s1 * rowBytes + ea = s2 * rowBytes + eb := by
          unfold s1 s2 at h_eq ⊢
          exact h_eq
        rw [h_eq1] at hlt1
        have : s2 * rowBytes + eb < s2 * rowBytes := by
          exact Nat.lt_of_le_of_lt h2_low hlt1
        omega
    | inr hgt =>
        have h_ge : s2 * rowBytes + rowBytes ≤ s1 * rowBytes := by
          have : s2 + 1 ≤ s1 := Nat.succ_le_of_lt hgt
          have : (s2 + 1) * rowBytes ≤ s1 * rowBytes := Nat.mul_le_mul_right _ this
          simpa [Nat.add_mul] using this
        have hlt2 : s2 * rowBytes + eb < s1 * rowBytes := by
          exact Nat.lt_of_lt_of_le h2_high h_ge
        have h_eq2 : s1 * rowBytes + ea = s2 * rowBytes + eb := by
          unfold s1 s2 at h_eq ⊢
          exact h_eq
        rw [h_eq2] at hlt2
        have : s1 * rowBytes + ea < s1 * rowBytes := by
          exact Nat.lt_of_le_of_lt h1_low hlt2
        omega

end GlimmerVerify.Bench
