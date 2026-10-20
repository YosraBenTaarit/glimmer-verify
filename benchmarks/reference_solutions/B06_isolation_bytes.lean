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
  intro h
  apply paged_kv_isolation A hiso hab ha hb
  have hS : 0 < rowBytes := by omega
  have key : ∀ x e, e < rowBytes → (x * rowBytes + e) / rowBytes = x := by
    intro x e he
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt he, Nat.zero_add]
  rw [← key (physSlot A.table a pa) ea hea, ← key (physSlot A.table b pb) eb heb, h]

end GlimmerVerify.Bench
