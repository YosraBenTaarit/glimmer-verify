import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def blockSize : Int := 16

def kernelSlot
    (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (req pos : Int)
    (table : Int → Int → Int) : Int :=
  if req >= 0 && req < num_reqs && pos >= 0 then
    let logical_block : Int := pos / 16
    if logical_block < max_blocks_per_req then
      let phys := table req logical_block
      if phys >= 0 && phys < num_physical_blocks then
        phys * 16 + pos % 16
      else
        -1
    else
      -1
  else
    -1

theorem kernel_slot_valid_or_sentinel
    (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (req pos : Int)
    (table : Int → Int → Int)
    (slot : Int)
    (hslot : slot = kernelSlot num_reqs max_blocks_per_req num_physical_blocks req pos table) :
    slot = -1 ∨ (0 ≤ slot ∧ slot < num_physical_blocks * 16) := by
  unfold kernelSlot at hslot
  simp only at hslot
  split at hslot
  · -- guard true
    rename_i hguard
    simp at hguard
    have hreq_ge : 0 ≤ req := hguard.1
    have hreq_lt : req < num_reqs := hguard.2.1
    have hpos_ge : 0 ≤ pos := hguard.2.2
    let logical_block : Int := pos / 16
    split at hslot with hlb
    · -- logical_block < max_blocks_per_req
      let phys := table req logical_block
      split at hslot with hphys
      · -- phys in range
        simp at hphys
        have hphys_ge : 0 ≤ phys := hphys.1
        have hphys_lt : phys < num_physical_blocks := hphys.2
        have hmod_ge : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
        right
        constructor
        · omega
        · omega
      · -- phys out of range
        left
        exact hslot.symm
    · -- logical_block >= max_blocks_per_req
      left
      exact hslot.symm
  · -- guard false
    left
    exact hslot.symm

end GlimmerVerify.Auto