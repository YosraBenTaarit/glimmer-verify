import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def kernelSlot (req pos : Int) (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (table : Int → Int → Int) : Int :=
  if h : req >= 0 ∧ req < num_reqs ∧ pos >= 0 then
    let logical_block := pos / 16
    if h2 : logical_block < max_blocks_per_req then
      let phys := table req logical_block
      if h3 : phys >= 0 ∧ phys < num_physical_blocks then
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
        have hpos : 0 ≤ pos := (hguard.2.2)
        have hphys_ge : 0 ≤ table req (pos / 16) := hphys.1
        have hphys_lt : table req (pos / 16) < num_physical_blocks := hphys.2
        have hmod_nn : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide)
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
        have hge : 0 ≤ table req (pos / 16) * 16 + pos % 16 := by
          have : 0 ≤ table req (pos / 16) * 16 := Int.mul_nonneg hphys_ge (by decide)
          omega
        have hlt : table req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
          have : table req (pos / 16) * 16 < num_physical_blocks * 16 :=
            Int.mul_lt_mul_of_pos_right hphys_lt (by decide)
          omega
        right
        exact ⟨hge, hlt⟩
    · rw [hslot]; left; rfl
  · rw [hslot]; left; rfl
  · rw [hslot]; left; rfl

end GlimmerVerify.Auto