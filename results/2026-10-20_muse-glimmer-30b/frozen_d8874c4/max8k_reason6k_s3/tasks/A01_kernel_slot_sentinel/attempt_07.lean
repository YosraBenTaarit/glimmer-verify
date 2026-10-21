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
  · rename_i hguard
    have hguard_eq : (decide (req ≥ 0) && decide (req < num_reqs) && decide (pos ≥ 0)) = true := hguard
    have hreq_ge : 0 ≤ req := by
      have := (decide_eq_true_iff.mp (by
        have : decide (req ≥ 0) = true := by
          have h1 : decide (req ≥ 0) && decide (req < num_reqs) && decide (pos ≥ 0) = true := hguard_eq
          have h2 : decide (req ≥ 0) = true := by
            by_cases h : decide (req ≥ 0) = true
            · exact h
            · simp [h] at h1
          exact h2
        exact this))
      exact this
    have hreq_lt : req < num_reqs := by
      have h1 : decide (req < num_reqs) = true := by
        have h2 : decide (req ≥ 0) = true := by
          by_cases h : decide (req ≥ 0) = true
          · exact h
          · simp [h] at hguard_eq
        have h3 : decide (req ≥ 0) && decide (req < num_reqs) = true := by
          have : decide (req ≥ 0) && decide (req < num_reqs) && decide (pos ≥ 0) = true := hguard_eq
          simp [h2] at this
          exact this
        exact (decide_eq_true_iff.mp (by
          cases h2; simp at h3; exact h3))
      exact (decide_eq_true_iff.mp h1)
    have hpos_ge : 0 ≤ pos := by
      have h1 : decide (pos ≥ 0) = true := by
        have h2 : decide (req ≥ 0) = true := by
          by_cases h : decide (req ≥ 0) = true
          · exact h
          · simp [h] at hguard_eq
        have h3 : decide (req < num_reqs) = true := by
          have : decide (req ≥ 0) && decide (req < num_reqs) = true := by
            have : decide (req ≥ 0) && decide (req < num_reqs) && decide (pos ≥ 0) = true := hguard_eq
            simp [h2] at this
            exact this
          exact (decide_eq_true_iff.mp (by
            cases h2; simp at this; exact this))
        have : decide (req ≥ 0) && decide (req < num_reqs) && decide (pos ≥ 0) = true := hguard_eq
        simp [h2, h3] at this
        exact this
      exact (decide_eq_true_iff.mp h1)
    let logical_block : Int := pos / 16
    split at hslot
    · rename_i hlb
      let phys := table req logical_block
      split at hslot
      · rename_i hphys
        have hphys_eq : (decide (phys ≥ 0) && decide (phys < num_physical_blocks)) = true := hphys
        have hphys_ge : 0 ≤ phys := by
          have : decide (phys ≥ 0) = true := by
            by_cases h : decide (phys ≥ 0) = true
            · exact h
            · simp [h] at hphys_eq
          exact (decide_eq_true_iff.mp this)
        have hphys_lt : phys < num_physical_blocks := by
          have h1 : decide (phys ≥ 0) = true := by
            by_cases h : decide (phys ≥ 0) = true
            · exact h
            · simp [h] at hphys_eq
          have h2 : decide (phys < num_physical_blocks) = true := by
            simp [h1] at hphys_eq
            exact hphys_eq
          exact (decide_eq_true_iff.mp h2)
        have hmod_ge : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
        have hslot_eq : slot = phys * 16 + pos % 16 := hslot
        right
        constructor
        · omega
        · omega
      · left
        exact hslot.symm
    · left
      exact hslot.symm
  · left
    exact hslot.symm

end GlimmerVerify.Auto