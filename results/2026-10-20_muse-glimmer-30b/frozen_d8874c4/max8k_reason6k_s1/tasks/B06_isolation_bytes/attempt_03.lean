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
  have h1_high : s1 * rowBytes + ea < s1 * rowBytes + rowBytes := by
    apply Nat.add_lt_add_left
    exact hea
  have h2_low : s2 * rowBytes ≤ s2 * rowBytes + eb := Nat.le_add_right _ _
  have h2_high : s2 * rowBytes + eb < s2 * rowBytes + rowBytes := by
    apply Nat.add_lt_add_left
    exact heb
  have hrow_pos : 0 < rowBytes := by
    omega
  by_cases hlt : s1 < s2
  · have h_ge : s1 * rowBytes + rowBytes ≤ s2 * rowBytes := by
      have : s1 + 1 ≤ s2 := Nat.succ_le_of_lt hlt
      have : (s1 + 1) * rowBytes ≤ s2 * rowBytes := Nat.mul_le_mul_right _ this
      simpa [Nat.add_mul] using this
    have : s1 * rowBytes + ea < s2 * rowBytes := by
      have : s1 * rowBytes + ea < s1 * rowBytes + rowBytes := h1_high
      exact Nat.lt_of_lt_of_le this h_ge
    rw [h_eq] at this
    have : s2 * rowBytes + eb < s2 * rowBytes := by
      exact Nat.lt_of_le_of_lt h2_low this
    omega
  · by_cases hgt : s2 < s1
    · have h_ge : s2 * rowBytes + rowBytes ≤ s1 * rowBytes := by
        have : s2 + 1 ≤ s1 := Nat.succ_le_of_lt hgt
        have : (s2 + 1) * rowBytes ≤ s1 * rowBytes := Nat.mul_le_mul_right _ this
        simpa [Nat.add_mul] using this
      have : s2 * rowBytes + eb < s1 * rowBytes := by
        have : s2 * rowBytes + eb < s2 * rowBytes + rowBytes := h2_high
        exact Nat.lt_of_lt_of_le this h_ge
      rw [h_eq] at this
      have : s1 * rowBytes + ea < s1 * rowBytes := by
        exact Nat.lt_of_le_of_lt h1_low this
      omega
    · have h_eq_s : s1 = s2 := Nat.le_antisymm (Nat.le_of_not_lt hlt) (Nat.le_of_not_lt hgt)
      rw [h_eq_s] at h_eq
      have : ea = eb := by omega
      subst this
      exact hslot_ne rfl

end GlimmerVerify.Bench
