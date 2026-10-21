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
  have hxa : physSlot A.table a pa * rowBytes ≤ physSlot A.table a pa * rowBytes + ea := Nat.le_add_right _ _
  have hxb : physSlot A.table b pb * rowBytes ≤ physSlot A.table b pb * rowBytes + eb := Nat.le_add_right _ _
  have hxa_up : physSlot A.table a pa * rowBytes + ea < (physSlot A.table a pa + 1) * rowBytes := by omega
  have hxb_up : physSlot A.table b pb * rowBytes + eb < (physSlot A.table b pb + 1) * rowBytes := by omega
  by_cases hlt : physSlot A.table a pa < physSlot A.table b pb
  · have : physSlot A.table a pa * rowBytes + ea < physSlot A.table b pb * rowBytes + eb := by omega
    contradiction
  · by_cases heq : physSlot A.table a pa = physSlot A.table b pb
    · rw [heq] at h
      have : ea = eb := by omega
                                                
      contradiction
    · have hgt : physSlot A.table b pb < physSlot A.table a pa := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
      have : physSlot A.table b pb * rowBytes + eb < physSlot A.table a pa * rowBytes + ea := by omega
      have : physSlot A.table a pa * rowBytes + ea = physSlot A.table b pb * rowBytes + eb := h
      omega

end GlimmerVerify.Bench
