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
  simp [kernelSlot]
  split_ifs with h1 h2 h3
  · have hpos : 0 ≤ pos := (h1).2.2
    have hmod_nn : 0 ≤ pos % 16 := Int.mod_nonneg pos (by decide)
    have hmod_lt : pos % 16 < 16 := Int.mod_lt pos (by decide)
    let phys := block_tables (req * max_blocks_per_req + pos / 16)
    have hphys_nn : 0 ≤ phys := (h3).1
    have hphys_lt : phys < num_physical_blocks := (h3).2
    have hslot_nn : 0 ≤ phys * 16 + pos % 16 := by omega
    have hslot_lt : phys * 16 + pos % 16 < num_physical_blocks * 16 := by omega
    exact Or.inr ⟨hslot_nn, hslot_lt⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

end GlimmerVerify.Auto