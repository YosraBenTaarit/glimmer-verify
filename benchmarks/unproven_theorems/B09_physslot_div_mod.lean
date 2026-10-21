import GlimmerVerify.PagedKVProofs

/-!
B09: invert the slot formula.

The kernel writes `phys * 16 + (pos & 15)`. Recovering the physical block and the in-block
offset from the slot is what the gather kernel does when it indexes `kv_cache[slot * row + e]`.
-/

namespace GlimmerVerify.Bench

open GlimmerVerify

theorem physSlot_div_mod (table : Nat → Nat → Nat) (req pos : Nat) :
    physSlot table req pos / blockSize = table req (pos / blockSize)
    ∧ physSlot table req pos % blockSize = pos % blockSize := by
  sorry

end GlimmerVerify.Bench
