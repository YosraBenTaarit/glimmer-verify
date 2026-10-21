import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def blockSize : Int := 16

def kernelSlot (req pos : Int) (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (table : Int → Int → Int) : Int :=
  if req >= 0 && req < num_reqs && pos >= 0 then
    let logical_block : Int := pos / 16
    if logical_block < max_blocks_per_req then
      let phys : Int := table req logical_block
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
    (table : Int → Int → Int) :
    let slot := kernelSlot req pos num_reqs max_blocks_per_req num_physical_blocks table
    slot = -1 ∨ (0 ≤ slot ∧ slot < num_physical_blocks * 16) := by
  simp only
  unfold kernelSlot
  split_ifs with hguard hlb hphys
  · -- all guards hold
    have hpos : 0 ≤ pos := by
      have := hguard.2.2
      exact this
    have hmod_nonneg : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide : (0: Int) < 16)
    have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide : (0: Int) < 16)
    have hphys_ge : 0 ≤ table req (pos / 16) := hphys.1
    have hphys_lt : table req (pos / 16) < num_physical_blocks := hphys.2
    have hslot_ge : 0 ≤ table req (pos / 16) * 16 + pos % 16 := by
      omega
    have hslot_lt : table req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
      omega
    right
    exact ⟨hslot_ge, hslot_lt⟩
  · -- phys guard fails
    left
    rfl
  · -- logical block guard fails
    left
    rfl
  · -- outer guard fails
    left
    rfl

end GlimmerVerify.Auto