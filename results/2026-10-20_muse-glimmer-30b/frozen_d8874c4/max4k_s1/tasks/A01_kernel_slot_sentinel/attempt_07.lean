import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def kernel_slot (req pos : Int) (table : Int → Int) (num_reqs max_blocks_per_req num_physical_blocks : Int) : Int :=
  if req >= 0 && req < num_reqs && pos >= 0 then
    let logical_block : Int := pos / 16
    if logical_block < max_blocks_per_req then
      let phys : Int := table (req * max_blocks_per_req + logical_block)
      if phys >= 0 && phys < num_physical_blocks then
        phys * 16 + pos % 16
      else -1
    else -1
  else -1

theorem kernel_slot_valid_or_sentinel (req pos : Int) (table : Int → Int) (num_reqs max_blocks_per_req num_physical_blocks : Int) :
  kernel_slot req pos table num_reqs max_blocks_per_req num_physical_blocks = -1 ∨
  0 ≤ kernel_slot req pos table num_reqs max_blocks_per_req num_physical_blocks ∧
  kernel_slot req pos table num_reqs max_blocks_per_req num_physical_blocks < num_physical_blocks * 16 := by
  unfold kernel_slot
  split
  · left; rfl
  · rename_i h1
    split
    · rename_i h2
      split
      · rename_i h3
        right
        have hpos : 0 ≤ pos := by
          have := (Int.and_imp.mp (by
            have := (Int.and_assoc _ _ _).symm
            rw [this] at h1
            exact h1)).2.2
          exact this
        have hphys_low : 0 ≤ phys := by
          have := (Int.and_imp.mp (by
            have := (Int.and_assoc _ _ _).symm
            rw [this] at h3
            exact h3)).1
          exact this
        have hphys_high : phys < num_physical_blocks := by
          have := (Int.and_imp.mp (by
            have := (Int.and_assoc _ _ _).symm
            rw [this] at h3
            exact h3)).2
          exact this
        have hmod : 0 ≤ pos % 16 := Int.emod_nonneg _ (by decide : (0: Int) < 16)
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos_right _ (by decide : (0: Int) < 16)
        have hslot_nonneg : 0 ≤ phys * 16 + pos % 16 := by
          apply Int.add_nonneg
          · apply Int.mul_nonneg
            · exact hphys_low
            · exact Int.zero_le _
          · exact hmod
        have hslot_lt : phys * 16 + pos % 16 < num_physical_blocks * 16 := by
          have h1 : phys * 16 ≤ num_physical_blocks * 16 - 16 := by
            have : phys * 16 < num_physical_blocks * 16 := by
              apply Int.mul_lt_mul_of_pos_right hphys_high (by decide : (0: Int) < 16)
              exact Int.zero_le _
            omega
          omega
        constructor
        · exact hslot_nonneg
        · exact hslot_lt
      · left; rfl
    · left; rfl

end GlimmerVerify.Auto