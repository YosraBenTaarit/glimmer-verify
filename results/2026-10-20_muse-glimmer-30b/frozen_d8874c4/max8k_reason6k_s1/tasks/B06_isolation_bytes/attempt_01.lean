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
  have hrow_pos : 0 < rowBytes := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_of_lt hea)
  have h_ea_lt : ea < rowBytes := hea
  have h_eb_lt : eb < rowBytes := heb
  have h_upper_a : physSlot A.table a pa * rowBytes + ea < physSlot A.table a pa * rowBytes + rowBytes := by
    omega
  have h_upper_b : physSlot A.table b pb * rowBytes + eb < physSlot A.table b pb * rowBytes + rowBytes := by
    omega
  have h_lower_a : physSlot A.table a pa * rowBytes ≤ physSlot A.table a pa * rowBytes + ea := by
    omega
  have h_lower_b : physSlot A.table b pb * rowBytes ≤ physSlot A.table b pb * rowBytes + eb := by
    omega
  by_cases hle : physSlot A.table a pa ≤ physSlot A.table b pb
  · have h1 : physSlot A.table a pa * rowBytes + ea ≤ physSlot A.table b pb * rowBytes + ea := by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_right _ hle
    have h2 : physSlot A.table b pb * rowBytes + ea < physSlot A.table b pb * rowBytes + rowBytes := by
      omega
    have h3 : physSlot A.table a pa * rowBytes + ea < physSlot A.table b pb * rowBytes + rowBytes := by
      exact Nat.lt_of_le_of_lt h1 h2
    have h4 : physSlot A.table a pa * rowBytes + ea = physSlot A.table b pb * rowBytes + eb := h_eq
    have h5 : physSlot A.table b pb * rowBytes + eb < physSlot A.table b pb * rowBytes + rowBytes := h_upper_b
    have h6 : physSlot A.table a pa * rowBytes + ea < physSlot A.table b pb * rowBytes + rowBytes := h3
                                                          
    by_cases hlt : physSlot A.table a pa < physSlot A.table b pb
    · have : physSlot A.table a pa * rowBytes + rowBytes ≤ physSlot A.table b pb * rowBytes := by
        have : physSlot A.table a pa + 1 ≤ physSlot A.table b pb := Nat.succ_le_of_lt hlt
        have : (physSlot A.table a pa + 1) * rowBytes ≤ physSlot A.table b pb * rowBytes := Nat.mul_le_mul_right _ this
        simpa [Nat.add_mul] using this
      have : physSlot A.table a pa * rowBytes + ea < physSlot A.table b pb * rowBytes := by
        have : physSlot A.table a pa * rowBytes + ea < physSlot A.table a pa * rowBytes + rowBytes := h_upper_a
        exact Nat.lt_of_lt_of_le this this
      rw [h_eq] at this
      have : physSlot A.table b pb * rowBytes + eb < physSlot A.table b pb * rowBytes := by
        exact this
      omega
    · have h_eq_slot : physSlot A.table a pa = physSlot A.table b pb := Nat.le_antisymm hle (Nat.le_of_not_lt hlt)
      rw [h_eq_slot] at h_eq
      omega
  · have hgt : physSlot A.table b pb < physSlot A.table a pa := Nat.lt_of_not_le hle
    have h1 : physSlot A.table b pb * rowBytes + eb ≤ physSlot A.table a pa * rowBytes + eb := by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt hgt)
    have h2 : physSlot A.table a pa * rowBytes + eb < physSlot A.table a pa * rowBytes + rowBytes := by
      omega
    have h3 : physSlot A.table b pb * rowBytes + eb < physSlot A.table a pa * rowBytes + rowBytes := by
      exact Nat.lt_of_le_of_lt h1 h2
    rw [h_eq] at h3
    have : physSlot A.table a pa * rowBytes + ea < physSlot A.table a pa * rowBytes + rowBytes := h_upper_a
    omega
  contradiction

end GlimmerVerify.Bench
