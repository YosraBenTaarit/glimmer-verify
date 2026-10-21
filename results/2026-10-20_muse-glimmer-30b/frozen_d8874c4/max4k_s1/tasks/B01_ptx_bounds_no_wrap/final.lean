import GlimmerVerify.PagedKVProofs

/-!
B01: 64-bit refinement of `GlimmerVerify.ptx_predicate_bounds_safe`.

PTX forms the address with `mul.wide.s32 %rd, %r, 4; add.s64 %rd, %rd_base, %rd`, which is
arithmetic modulo 2^64. If the whole buffer `[base, base + 4n)` fits in the address space, the
address of every lane that passes `%p1 : i < n` does not wrap and stays in bounds.
-/

namespace GlimmerVerify.Bench

theorem ptx_bounds_no_wrap (base n i : Nat) (hfit : base + 4 * n ≤ 2 ^ 64) (hp1 : i < n) :
    (base + 4 * i) % 2 ^ 64 = base + 4 * i ∧ base + 4 * i + 4 ≤ base + 4 * n := by
  have hlt64 : base + 4 * i < 2 ^ 64 := by omega
  constructor
  · exact Nat.mod_eq_of_lt hlt64
  · omega

end GlimmerVerify.Bench
