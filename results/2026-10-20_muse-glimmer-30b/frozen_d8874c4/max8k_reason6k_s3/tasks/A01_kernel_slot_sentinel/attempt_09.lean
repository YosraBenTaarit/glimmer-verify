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
  by_cases hreq_ge : req >= 0
  by_cases hreq_lt : req < num_reqs
  by_cases hpos_ge : pos >= 0
  · have hguard : (req >= 0 && req < num_reqs && pos >= 0) = true := by
      simp [hreq_ge, hreq_lt, hpos_ge]
    rw [if_pos hguard] at hslot
    let logical_block : Int := pos / 16
    by_cases hlb : logical_block < max_blocks_per_req
    · rw [if_pos hlb] at hslot
      let phys := table req logical_block
      by_cases hphys_ge : phys >= 0
      by_cases hphys_lt : phys < num_physical_blocks
      · have hphys : (phys >= 0 && phys < num_physical_blocks) = true := by
          simp [hphys_ge, hphys_lt]
        rw [if_pos hphys] at hslot
        have hmod_ge : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
        have hslot_eq : slot = phys * 16 + pos % 16 := hslot
        right
        constructor
        · omega
        · omega
      · have hphys_false : (phys >= 0 && phys < num_physical_blocks) = false := by
          simp [hphys_ge, hphys_lt]
        rw [if_neg hphys_false] at hslot
        left
        exact hslot.symm
      · have hphys_false : (phys >= 0 && phys < num_physical_blocks) = false := by
          simp [hphys_ge, hphys_lt]
        rw [if_neg hphys_false] at hslot
        left
        exact hslot.symm
    · rw [if_neg hlb] at hslot
      left
      exact hslot.symm
  · have hguard : (req >= 0 && req < num_reqs && pos >= 0) = false := by
      simp [hreq_ge, hreq_lt]
    rw [if_neg hguard] at hslot
    left
    exact hslot.symm
  · have hguard : (req >= 0 && req < num_reqs && pos >= 0) = false := by
      simp [hreq_ge, hreq_lt, hpos_ge]
    rw [if_neg hguard] at hslot
    left
    exact hslot.symm
  · have hguard : (req >= 0 && req < num_reqs && pos >= 0) = false := by
      simp [hreq_ge, hreq_lt]
    rw [if_neg hguard] at hslot
    left
    exact hslot.symm

end GlimmerVerify.Auto