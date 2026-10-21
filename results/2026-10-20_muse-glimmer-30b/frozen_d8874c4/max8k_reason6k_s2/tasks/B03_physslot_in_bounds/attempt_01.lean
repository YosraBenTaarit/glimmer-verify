import GlimmerVerify.PagedKVProofs

/-!
B03: every slot produced by the indexer lies inside the physical KV pool.

If every page-table entry names one of the `numPhys` physical blocks (the kernel checks
`phys < num_physical_blocks`), then `physSlot` is below `numPhys * blockSize`, so the
`kv_cache[slot * row_elems + e]` read in `paged_kv_gather_kernel` is in bounds.
-/

namespace GlimmerVerify.Bench

open GlimmerVerify

theorem physSlot_lt_capacity (table : Nat → Nat → Nat) (numPhys req pos : Nat)
    (hpt : ∀ r l, table r l < numPhys) :
    physSlot table req pos < numPhys * blockSize := by
  unfold physSlot
  have htbl : table req (pos / blockSize) < numPhys := hpt req (pos / blockSize)
  have hmod : pos % blockSize < blockSize := Nat.mod_lt pos (by decide)
  unfold blockSize
  omega

end GlimmerVerify.Bench
