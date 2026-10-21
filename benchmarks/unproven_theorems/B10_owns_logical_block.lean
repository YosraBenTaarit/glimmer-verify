import GlimmerVerify.PagedKVProofs

/-!
B10: `Owns` is the kernel's logical-block check.

`pos < numBlocks * 16` if and only if the logical block `pos / 16` is one of the blocks
allocated to the request, which is the `logical_block < max_blocks_per_req` guard in
`paged_kv_index_kernel` when `numBlocks` is the allocated length (unallocated table entries
are the `-1` padding).
-/

namespace GlimmerVerify.Bench

open GlimmerVerify

theorem owns_iff_logical_in_range (A : KVAllocator) (req pos : Nat) :
    A.Owns req pos ↔ pos / blockSize < A.numBlocks req := by
  sorry

end GlimmerVerify.Bench
