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
  have h1 : s1 * rowBytes ≤ s1 * rowBytes + ea := Nat.le_add_right _ _
  have h2 : s1 * rowBytes + ea < s1 * rowBytes + rowBytes := Nat.add_lt_add_left hea _
  have h3 : s1 * rowBytes + rowBytes = (s1 + 1) * rowBytes := by ring
  have h4 : s1 * rowBytes + ea < (s1 + 1) * rowBytes := by rw [← h3]; exact h2
  have h5 : s2 * rowBytes ≤ s2 * rowBytes + eb := Nat.le_add_right _ _
  have h6 : s2 * rowBytes + eb < s2 * rowBytes + rowBytes := Nat.add_lt_add_left heb _
  have h7 : s2 * rowBytes + rowBytes = (s2 + 1) * rowBytes := by ring
  have h8 : s2 * rowBytes + eb < (s2 + 1) * rowBytes := by rw [← h7]; exact h6
                                                                     
  have h_eq' : s1 * rowBytes + ea = s2 * rowBytes + eb := h_eq
                                               
  have h_le1 : s1 ≤ s2 := by
    have : s1 * rowBytes ≤ s1 * rowBytes + ea := h1
    have : s1 * rowBytes + ea = s2 * rowBytes + eb := h_eq'
    have : s1 * rowBytes ≤ s2 * rowBytes + eb := by trans s1 * rowBytes + ea; exact this
    have : s1 * rowBytes < (s2 + 1) * rowBytes := by
      have : s1 * rowBytes ≤ s2 * rowBytes + eb := by
        trans s1 * rowBytes + ea; exact this
      have : s2 * rowBytes + eb < (s2 + 1) * rowBytes := h8
      exact Nat.lt_of_le_of_lt this this
    omega
  have h_le2 : s2 ≤ s1 := by
    have : s2 * rowBytes ≤ s2 * rowBytes + eb := h5
    have : s2 * rowBytes + eb = s1 * rowBytes + ea := by rw [h_eq']
    have : s2 * rowBytes ≤ s1 * rowBytes + ea := by trans s2 * rowBytes + eb; exact this
    have : s2 * rowBytes < (s1 + 1) * rowBytes := by
      have : s2 * rowBytes ≤ s1 * rowBytes + ea := by
        trans s2 * rowBytes + eb; exact this
      have : s1 * rowBytes + ea < (s1 + 1) * rowBytes := h4
      exact Nat.lt_of_le_of_lt this this
    omega
  have h_eq_slots : s1 = s2 := Nat.le_antisymm h_le1 h_le2
  contradiction

end GlimmerVerify.Bench
