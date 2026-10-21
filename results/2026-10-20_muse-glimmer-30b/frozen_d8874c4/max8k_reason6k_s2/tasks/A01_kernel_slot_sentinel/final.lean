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
      · simp [h1, h2, h3] at hslot
        by_cases hl : pos / 16 < max_blocks_per_req
        · simp [hl] at hslot
          by_cases h4 : table req (pos / 16) >= 0
          · by_cases h5 : table req (pos / 16) < num_physical_blocks
            · simp [h4, h5] at hslot
              have hmod_nn : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide)
              have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
              have hge : 0 ≤ table req (pos / 16) * 16 + pos % 16 := by
                have : 0 ≤ table req (pos / 16) * 16 := Int.mul_nonneg h4 (by decide)
                omega
              have hlt : table req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
                have : table req (pos / 16) * 16 < num_physical_blocks * 16 :=
                  Int.mul_lt_mul_of_pos_right h5 (by decide)
                omega
              rw [hslot]
              right; exact ⟨hge, hlt⟩
            · simp [h4, h5] at hslot
              rw [hslot]; left; rfl
          · simp [h4] at hslot
            rw [hslot]; left; rfl
        · simp [hl] at hslot
          rw [hslot]; left; rfl
      · simp [h1, h2, h3] at hslot
        rw [hslot]; left; rfl
    · simp [h1, h2] at hslot
      rw [hslot]; left; rfl
  · simp [h1] at hslot
    rw [hslot]; left; rfl

end GlimmerVerify.Auto