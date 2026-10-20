/-!
# Safety theorems for the paged KV-cache indexer

Models of `src/runtime/paged_kv_indexer.cu`. Arithmetic is over `Nat`, i.e. unbounded;
the 64-bit no-wrap refinement is benchmark task `B01_ptx_bounds_no_wrap`.

* `ptx_predicate_bounds_safe`: a lane that passes the PTX guard `%p1` only touches
  `[base, base + 4 * n)`.
* `paged_kv_isolation`: requests whose allocated page-table entries are disjoint never map a
  token to the same physical KV slot.
-/

namespace GlimmerVerify

/-- Tokens per KV-cache block (`kKVBlockSize`, vLLM `--block-size 16`). -/
def blockSize : Nat := 16

/-! ## PTX predicate `%p1` -/

/-- Global lane index `%ctaid.x * %ntid.x + %tid.x`. -/
def globalIdx (blockIdx blockDim threadIdx : Nat) : Nat :=
  blockIdx * blockDim + threadIdx

/-- Byte address of 32-bit element `i` of a buffer starting at `base`. -/
def elemAddr (base i : Nat) : Nat :=
  base + 4 * i

/-- Address of the lane's guarded 32-bit access, or `none` when
`setp.ge %p1, idx, n; @%p1 bra $L_exit;` masks the lane off. -/
def guardedAccess (base n i : Nat) : Option Nat :=
  if i < n then some (elemAddr base i) else none

/-- Every byte touched by a lane that survives `%p1` lies inside `[base, base + 4 * n)`. -/
theorem ptx_predicate_bounds_safe (base n bIdx bDim tIdx addr : Nat)
    (h : guardedAccess base n (globalIdx bIdx bDim tIdx) = some addr) :
    base ≤ addr ∧ addr + 4 ≤ base + 4 * n := by
  unfold guardedAccess at h
  split at h
  · cases h
    unfold elemAddr
    omega
  · cases h

/-- The same fact stated directly on the guard hypothesis `%p1 : i < n`. -/
theorem ptx_predicate_bounds_safe_of_guard (base n bIdx bDim tIdx : Nat)
    (hp1 : globalIdx bIdx bDim tIdx < n) :
    elemAddr base (globalIdx bIdx bDim tIdx) + 4 ≤ base + 4 * n := by
  unfold elemAddr
  omega

/-! ## Paged KV-cache isolation -/

/-- Allocator state: `table req l` is the physical block backing logical block `l` of request
`req`, and `numBlocks req` is how many logical blocks `req` has been given. Entries at
`l ≥ numBlocks req` are unconstrained, like the `-1` padding in the runtime's block table. -/
structure KVAllocator where
  table : Nat → Nat → Nat
  numBlocks : Nat → Nat

/-- Physical token slot of position `pos` of request `req`; the kernel's
`phys * kKVBlockSize + (pos & (kKVBlockSize - 1))`. -/
def physSlot (table : Nat → Nat → Nat) (req pos : Nat) : Nat :=
  table req (pos / blockSize) * blockSize + pos % blockSize

/-- Distinct requests never share an allocated physical block. -/
def KVAllocator.Isolated (A : KVAllocator) : Prop :=
  ∀ a b, a ≠ b → ∀ la lb, la < A.numBlocks a → lb < A.numBlocks b → A.table a la ≠ A.table b lb

/-- Position `pos` lies inside the blocks allocated to `req`. -/
def KVAllocator.Owns (A : KVAllocator) (req pos : Nat) : Prop :=
  pos < A.numBlocks req * blockSize

/-- Cross-tenant isolation: two different requests never read or write the same KV slot. -/
theorem paged_kv_isolation (A : KVAllocator) (hiso : A.Isolated) {a b pa pb : Nat}
    (hab : a ≠ b) (ha : A.Owns a pa) (hb : A.Owns b pb) :
    physSlot A.table a pa ≠ physSlot A.table b pb := by
  unfold KVAllocator.Owns blockSize at ha hb
  have hblk := hiso a b hab (pa / 16) (pb / 16) (by omega) (by omega)
  unfold physSlot blockSize
  omega

end GlimmerVerify
