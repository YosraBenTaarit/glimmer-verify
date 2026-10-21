import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def kernelSlot (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (block_tables : Int → Int) (req pos : Int) : Int :=
  if req >= 0 && req < num_reqs && pos >= 0 then
    let logical_block := pos / 16
    if logical_block < max_blocks_per_req then
      let phys := block_tables (req * max_blocks_per_req + logical_block)
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
    (block_tables : Int → Int) (req pos : Int) :
    let slot := kernelSlot num_reqs max_blocks_per_req num_physical_blocks block_tables req pos
    slot = -1 ∨ (0 ≤ slot ∧ slot < num_physical_blocks * 16) := by
  unfold kernelSlot
  by_cases h1 : req >= 0 && req < num_reqs && pos >= 0
  · by_cases h2 : pos / 16 < max_blocks_per_req
    · let phys := block_tables (req * max_blocks_per_req + pos / 16)
      by_cases h3 : phys >= 0 && phys < num_physical_blocks
      · have hpos : 0 ≤ pos := by
          have : req >= 0 && req < num_reqs && pos >= 0 := h1
          simp at this
          exact this.2
        have hphys_nn : 0 ≤ phys := by
          simp at h3
          exact h3.1
        have hphys_lt : phys < num_physical_blocks := by
          simp at h3
          exact h3.2
        have hmod_nn : 0 ≤ pos % 16 := by omega
        have hmod_lt : pos % 16 < 16 := by omega
        simp [h1, h2, h3]
        have hslot_nn : 0 ≤ phys * 16 + pos % 16 := by omega
        have hslot_lt : phys * 16 + pos % 16 < num_physical_blocks * 16 := by omega
        exact Or.inr ⟨hslot_nn, hslot_lt⟩
      · simp [h1, h2, h3]
        exact Or.inl rfl
    · simp [h1, h2]
      exact Or.inl rfl
  · simp [h1]
    exact Or.inl rfl

end GlimmerVerify.Auto