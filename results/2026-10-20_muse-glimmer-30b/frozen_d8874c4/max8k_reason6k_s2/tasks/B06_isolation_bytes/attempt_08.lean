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
  have h_ea : ea < rowBytes := hea
  have h_eb : eb < rowBytes := heb
  have h1 : s1 * rowBytes ≤ s1 * rowBytes + ea := Nat.le_add_right _ _
  have h2 : s1 * rowBytes + ea < s1 * rowBytes + rowBytes := Nat.add_lt_add_left h_ea _
  have h3 : s2 * rowBytes ≤ s2 * rowBytes + eb := Nat.le_add_right _ _
  have h4 : s2 * rowBytes + eb < s2 * rowBytes + rowBytes := Nat.add_lt_add_left h_eb _
  have h_mul : s1 * rowBytes + ea = s2 * rowBytes + eb := h_eq
                                                                                    
  omega

end GlimmerVerify.Bench
