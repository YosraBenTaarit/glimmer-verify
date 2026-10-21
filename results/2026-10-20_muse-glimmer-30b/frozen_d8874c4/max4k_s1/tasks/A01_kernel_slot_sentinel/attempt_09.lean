import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def kernel_slot (req pos : Int) (table : Int → Int) (num_reqs max_blocks_per_req num_physical_blocks : Int) : Int :=
  if req >= 0 ∧ req < num_reqs ∧ pos >= 0 then
    if pos / 16 < max_blocks_per_req then
      let phys := table (req * max_blocks_per_req + pos / 16)
      if phys >= 0 ∧ phys < num_physical_blocks then
        phys * 16 + pos % 16
      else -1
    else -1
  else -1

theorem kernel_slot_valid_or_sentinel (req pos : Int) (table : Int → Int) (num_reqs max_blocks_per_req num_physical_blocks : Int) :
  kernel_slot req pos table num_reqs max_blocks_per_req num_physical_blocks = -1 ∨
  (0 ≤ kernel_slot req pos table num_reqs max_blocks_per_req num_physical_blocks ∧
   kernel_slot req pos table num_reqs max_blocks_per_req num_physical_blocks < num_physical_blocks * 16) := by
  unfold kernel_slot
  by_cases h0 : req >= 0 ∧ req < num_reqs ∧ pos >= 0
  · by_cases h1 : pos / 16 < max_blocks_per_req
    · let phys := table (req * max_blocks_per_req + pos / 16)
      by_cases h2 : phys >= 0 ∧ phys < num_physical_blocks
      · simp [h0, h1, h2]
        right
        have hmod_nn : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos_right pos (by decide : (0 : Int) < 16)
        constructor
        · apply Int.add_nonneg
          · apply Int.mul_nonneg
            · exact h2.1
            · exact Int.zero_le _
          · exact hmod_nn
        · have : phys * 16 < num_physical_blocks * 16 := Int.mul_lt_mul_of_pos_right h2.2 (by decide : (0 : Int) < 16)
          omega
      · simp [h0, h1, h2]; left; rfl
    · simp [h0, h1]; left; rfl
  · simp [h0]; left; rfl

end GlimmerVerify.Auto