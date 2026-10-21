import GlimmerVerify.PagedKVProofs

/-!
B04: warp-level coalescing of `req_ids[idx]` / `token_pos[idx]` loads.

With `blockDim = 32`, the 32 lanes of warp `w` read 4-byte elements at `elemAddr base (globalIdx w 32 lane)`.
All of them fall inside the single 128-byte segment `[base + 128 w, base + 128 (w + 1))`,
so the warp issues one memory transaction (for a 128-byte-aligned `base`).
-/

namespace GlimmerVerify.Bench

open GlimmerVerify

theorem warp_access_coalesced (base w lane : Nat) (hlane : lane < 32) :
    base + 128 * w ≤ elemAddr base (globalIdx w 32 lane) ∧
      elemAddr base (globalIdx w 32 lane) + 4 ≤ base + 128 * (w + 1) := by
  unfold elemAddr globalIdx
  simp
  omega

end GlimmerVerify.Bench
