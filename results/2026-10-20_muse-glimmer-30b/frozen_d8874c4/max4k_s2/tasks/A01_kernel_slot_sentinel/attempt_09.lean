import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def kernelSlot (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (block_tables : Int → Int) (req pos : Int) : Int :=
  if h : req >= 0 ∧ req < num_reqs ∧ pos >= 0 then
    if h2 : pos / 16 < max_blocks_per_req then
      let phys := block_tables (req * max_blocks_per_req + pos / 16)
      if h3 : phys >= 0 ∧ phys < num_physical_blocks then
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
  by_cases h : req >= 0 ∧ req < num_reqs ∧ pos >= 0
  · have hpos : 0 ≤ pos := h.2.2
    by_cases h2 : pos / 16 < max_blocks_per_req
    · let phys := block_tables (req * max_blocks_per_req + pos / 16)
      by_cases h3 : phys >= 0 ∧ phys < num_physical_blocks
      · simp [h, h2, h3]
        exact Or.inr ⟨by omega, by omega⟩
      · simp [h, h2, h3]
        exact Or.inl rfl
    · simp [h, h2]
      exact Or.inl rfl
  · simp [h]
    exact Or.inl rfl

end GlimmerVerify.Auto