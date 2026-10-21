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
  by_cases hguard : req >= 0 ∧ req < num_reqs ∧ pos >= 0
  · have hguard' : (req >= 0 && req < num_reqs && pos >= 0) = true := by
      simp [hguard]
    rw [hguard'] at hslot
    simp at hslot
    let logical_block : Int := pos / 16
    by_cases hlb : logical_block < max_blocks_per_req
    · rw [if_pos hlb] at hslot
      let phys := table req logical_block
      by_cases hphys : phys >= 0 ∧ phys < num_physical_blocks
      · have hphys' : (phys >= 0 && phys < num_physical_blocks) = true := by simp [hphys]
        rw [if_pos hphys'] at hslot
        have hmod_ge : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
        have hphys_ge : 0 ≤ phys := hphys.1
        have hphys_lt : phys < num_physical_blocks := hphys.2
        have hpos_ge : 0 ≤ pos := hguard.2.2
        have hslot_eq : slot = phys * 16 + pos % 16 := hslot
        right
        constructor
        · omega
        · omega
      · have hphys' : ¬(phys >= 0 && phys < num_physical_blocks) := by
          intro h
          exact hphys (by simp [h])
        rw [if_neg hphys'] at hslot
        left
        exact hslot.symm
    · rw [if_neg hlb] at hslot
      left
      exact hslot.symm
  · have hguard' : ¬(req >= 0 ∧ req < num_reqs ∧ pos >= 0) := hguard
    have hcond : ¬(req >= 0 && req < num_reqs && pos >= 0) := by
      intro h
      have : req >= 0 ∧ req < num_reqs ∧ pos >= 0 := by
        simp at h
        exact ⟨h.1, ⟨h.2.1, h.2.2⟩⟩
      exact hguard' this
    have hif : (if req >= 0 && req < num_reqs && pos >= 0 then
        let logical_block : Int := pos / 16
        if logical_block < max_blocks_per_req then
          let phys := table req logical_block
          if phys >= 0 && phys < num_physical_blocks then
            phys * 16 + pos % 16
          else
            -1
        else
          -1
      else -1) = -1 := by
      simp [hcond]
    rw [hif] at hslot
    left
    exact hslot.symm

end GlimmerVerify.Auto