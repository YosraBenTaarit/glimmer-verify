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
  split at hslot with hguard
  · split at hslot with hlb
    · split at hslot with hphys
      · rw [hslot]
        have hpos : 0 ≤ pos := by
          have := (hguard).2.1
          omega
        have hlb_ge : 0 ≤ pos / 16 := by
          apply Int.div_nonneg hpos (by decide)
        have hphys_ge : 0 ≤ table req (pos / 16) := by
          have := (hphys).1
          omega
        have hphys_lt : table req (pos / 16) < num_physical_blocks := by
          have := (hphys).2
          omega
        have hmod : 0 ≤ pos % 16 ∧ pos % 16 < 16 := by
          have h1 : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide)
          have h2 : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
          exact ⟨h1, h2⟩
        have hslot_ge : 0 ≤ table req (pos / 16) * 16 + pos % 16 := by
          have : 0 ≤ table req (pos / 16) * 16 := by
            apply Int.mul_nonneg hphys_ge (by decide)
          omega
        have hslot_lt : table req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
          have : table req (pos / 16) * 16 < num_physical_blocks * 16 := by
            apply Int.mul_lt_mul_of_pos_right hphys_lt (by decide)
          omega
        right
        exact ⟨hslot_ge, hslot_lt⟩
      · rw [hslot]
        left; rfl
    · rw [hslot]
      left; rfl
  · rw [hslot]
    left; rfl

end GlimmerVerify.Auto