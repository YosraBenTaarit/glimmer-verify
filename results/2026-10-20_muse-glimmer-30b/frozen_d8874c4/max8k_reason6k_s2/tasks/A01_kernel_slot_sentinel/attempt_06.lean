import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def kernelSlot (req pos : Int) (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (table : Int → Int → Int) : Int :=
  if req >= 0 && req < num_reqs && pos >= 0 then
    let logical_block := pos / 16
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
    (req pos : Int) (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (table : Int → Int → Int)
    (slot : Int)
    (hslot : slot = kernelSlot req pos num_reqs max_blocks_per_req num_physical_blocks table) :
    slot = -1 ∨ (0 ≤ slot ∧ slot < num_physical_blocks * 16) := by
  unfold kernelSlot at hslot
  by_cases h1 : req >= 0
  · by_cases h2 : req < num_reqs
    · by_cases h3 : pos >= 0
      · have hguard : req >= 0 && req < num_reqs && pos >= 0 = true := by
          simp [h1, h2, h3]
        rw [if_pos hguard] at hslot
        by_cases hlb : pos / 16 < max_blocks_per_req
        · rw [if_pos hlb] at hslot
          by_cases h4 : table req (pos / 16) >= 0
          · by_cases h5 : table req (pos / 16) < num_physical_blocks
            · have hphys : table req (pos / 16) >= 0 && table req (pos / 16) < num_physical_blocks = true := by
                simp [h4, h5]
              rw [if_pos hphys] at hslot
              have hmod_nn : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide)
              have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
              have hphys_nn : 0 ≤ table req (pos / 16) := h4
              have hphys_lt : table req (pos / 16) < num_physical_blocks := h5
              have hge : 0 ≤ table req (pos / 16) * 16 + pos % 16 := by
                have : 0 ≤ table req (pos / 16) * 16 := Int.mul_nonneg hphys_nn (by decide)
                omega
              have hlt : table req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
                have : table req (pos / 16) * 16 < num_physical_blocks * 16 :=
                  Int.mul_lt_mul_of_pos_right hphys_lt (by decide)
                omega
              rw [hslot]
              right; exact ⟨hge, hlt⟩
            · have hphys : table req (pos / 16) >= 0 && table req (pos / 16) < num_physical_blocks = false := by
                simp [h4, h5]
              rw [if_neg hphys] at hslot
              rw [hslot]; left; rfl
          · have hphys : table req (pos / 16) >= 0 && table req (pos / 16) < num_physical_blocks = false := by
              simp [h4]
            rw [if_neg hphys] at hslot
            rw [hslot]; left; rfl
        · rw [if_neg hlb] at hslot
          rw [hslot]; left; rfl
      · have hguard : req >= 0 && req < num_reqs && pos >= 0 = false := by
          simp [h1, h2, h3]
        rw [if_neg hguard] at hslot
        rw [hslot]; left; rfl
    · have hguard : req >= 0 && req < num_reqs && pos >= 0 = false := by
        simp [h1, h2]
      rw [if_neg hguard] at hslot
      rw [hslot]; left; rfl
  · have hguard : req >= 0 && req < num_reqs && pos >= 0 = false := by
      simp [h1]
    rw [if_neg hguard] at hslot
    rw [hslot]; left; rfl

end GlimmerVerify.Auto