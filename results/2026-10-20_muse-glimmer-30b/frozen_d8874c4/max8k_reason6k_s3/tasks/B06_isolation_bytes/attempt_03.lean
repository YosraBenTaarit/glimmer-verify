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
  have hne : physSlot A.table a pa ≠ physSlot A.table b pb :=
    paged_kv_isolation A hiso hab ha hb
  have hrow_pos : 0 < rowBytes := by omega
  intro h
  let s1 := physSlot A.table a pa
  let s2 := physSlot A.table b pb
  have h1_lt : s1 * rowBytes + ea < s1 * rowBytes + rowBytes := Nat.add_lt_add_left hea _
  rw [Nat.mul_succ] at h1_lt
  have h1_up : s1 * rowBytes + ea < (s1 + 1) * rowBytes := h1_lt
  have h2_lt : s2 * rowBytes + eb < s2 * rowBytes + rowBytes := Nat.add_lt_add_left heb _
  rw [Nat.mul_succ] at h2_lt
  have h2_up : s2 * rowBytes + eb < (s2 + 1) * rowBytes := h2_lt
  have h1_low : s1 * rowBytes ≤ s1 * rowBytes + ea := Nat.le_add_right _ _
  have h2_low : s2 * rowBytes ≤ s2 * rowBytes + eb := Nat.le_add_right _ _
  rw [h] at h1_low h1_up h2_low h2_up
  have hle1 : s2 * rowBytes ≤ s1 * rowBytes + ea := h1_low
  have hlt1 : s2 * rowBytes + eb < (s1 + 1) * rowBytes := h1_up
  have hle2 : s1 * rowBytes ≤ s2 * rowBytes + eb := h2_low
  have hlt2 : s1 * rowBytes + ea < (s2 + 1) * rowBytes := h2_up
  have hlt_s2 : s2 * rowBytes < (s1 + 1) * rowBytes := Nat.lt_of_le_of_lt hle1 hlt1
  have hlt_s1 : s1 * rowBytes < (s2 + 1) * rowBytes := Nat.lt_of_le_of_lt hle2 hlt2
  have h_s2_le : s2 < s1 + 1 := by
    have : s2 * rowBytes < (s1 + 1) * rowBytes := hlt_s2
    exact Nat.mul_lt_mul_right.mp this hrow_pos
  have h_s1_le : s1 < s2 + 1 := by
    have : s1 * rowBytes < (s2 + 1) * rowBytes := hlt_s1
    exact Nat.mul_lt_mul_right.mp this hrow_pos
  have h_eq : s1 = s2 := by omega
  rw [h_eq] at h
  have : ea = eb := by omega
  contradiction

end GlimmerVerify.Bench
