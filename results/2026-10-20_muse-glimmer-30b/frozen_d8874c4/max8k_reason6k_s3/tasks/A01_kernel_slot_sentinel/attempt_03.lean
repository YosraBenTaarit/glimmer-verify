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
  split_ifs at hslot with hguard hlb hphys
  · -- guard true, logical_block < max, phys in range
    have hpos_ge : 0 ≤ pos := by
      have : req >= 0 && req < num_reqs && pos >= 0 = true := hguard
      simp at this
      exact this.2.2
    have hphys_ge : 0 ≤ table req (pos / 16) := by
      have : table req (pos / 16) >= 0 && table req (pos / 16) < num_physical_blocks = true := hphys
      simp at this
      exact this.1
    have hphys_lt : table req (pos / 16) < num_physical_blocks := by
      have : table req (pos / 16) >= 0 && table req (pos / 16) < num_physical_blocks = true := hphys
      simp at this
      exact this.2
    have hmod_ge : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
    have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
    have hslot_eq : slot = table req (pos / 16) * 16 + pos % 16 := hslot
    right
    constructor
    · omega
    · omega
  · -- guard true, logical_block < max, phys out of range
    left
    exact hslot.symm
  · -- guard true, logical_block >= max
    left
    exact hslot.symm
  · -- guard false
    left
    exact hslot.symm

end GlimmerVerify.Auto