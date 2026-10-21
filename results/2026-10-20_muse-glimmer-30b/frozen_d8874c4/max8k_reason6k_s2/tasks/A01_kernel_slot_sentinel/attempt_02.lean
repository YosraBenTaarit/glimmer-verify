import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def blockSizeInt : Int := 16

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
  split_ifs at hslot with hguard hlb hphys
  · -- guard true, logical_block < max_blocks_per_req, phys in range
    rw [hslot]
    have hpos : 0 ≤ pos := by
      have : req ≥ 0 ∧ req < num_reqs ∧ pos ≥ 0 := hguard
      exact (this.2.2)
    have hphys_ge : 0 ≤ table req (pos / 16) := by
      have : table req (pos / 16) ≥ 0 ∧ table req (pos / 16) < num_physical_blocks := hphys
      exact this.1
    have hphys_lt : table req (pos / 16) < num_physical_blocks := by
      have : table req (pos / 16) ≥ 0 ∧ table req (pos / 16) < num_physical_blocks := hphys
      exact this.2
    have hmod_nonneg : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide)
    have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
    have hslot_ge : 0 ≤ table req (pos / 16) * 16 + pos % 16 := by
      have h1 : 0 ≤ table req (pos / 16) * 16 := Int.mul_nonneg hphys_ge (by decide)
      omega
    have hslot_lt : table req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
      have h1 : table req (pos / 16) * 16 < num_physical_blocks * 16 := Int.mul_lt_mul_of_pos_right hphys_lt (by decide)
      omega
    right
    exact ⟨hslot_ge, hslot_lt⟩
  · -- guard true, logical_block ≥ max_blocks_per_req
    rw [hslot]
    left; rfl
  · -- guard true, logical_block < max_blocks_per_req, phys out of range
    rw [hslot]
    left; rfl
  · -- guard false
    rw [hslot]
    left; rfl

end GlimmerVerify.Auto