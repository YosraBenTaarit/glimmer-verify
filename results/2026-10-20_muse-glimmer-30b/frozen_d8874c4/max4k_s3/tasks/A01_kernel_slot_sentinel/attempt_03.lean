import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def kernelSlot
  (num_reqs max_blocks_per_req num_physical_blocks : Int)
  (req pos : Int)
  (getPhys : Int → Int → Int) : Int :=
  if req ≥ 0 ∧ req < num_reqs ∧ pos ≥ 0 then
    let logical_block := pos / 16
    if logical_block < max_blocks_per_req then
      let phys := getPhys req logical_block
      if phys ≥ 0 ∧ phys < num_physical_blocks then
        phys * 16 + pos % 16
      else
        -1
    else
      -1
  else
    -1

theorem kernel_slot_valid_or_sentinel
  (num_reqs max_blocks_per_req num_physical_blocks : Int)
  (req pos : Int)
  (getPhys : Int → Int → Int) :
  let s := kernelSlot num_reqs max_blocks_per_req num_physical_blocks req pos getPhys
  s = -1 ∨ 0 ≤ s ∧ s < num_physical_blocks * 16 := by
  unfold kernelSlot
  split
  · split
    · split
      · have hphys : 0 ≤ getPhys req (pos / 16) := by
          have h := ‹phys ≥ 0 ∧ phys < num_physical_blocks›
          exact h.1
      · have hphys_lt : getPhys req (pos / 16) < num_physical_blocks := by
          have h := ‹phys ≥ 0 ∧ phys < num_physical_blocks›
          exact h.2
        have hmod : 0 ≤ pos % 16 := Int.emod_nonneg _ (by decide)
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos _ (by decide)
        have hpos : 0 ≤ pos := by
          have h := ‹req ≥ 0 ∧ req < num_reqs ∧ pos ≥ 0›
          exact h.2.2
        have hslot : 0 ≤ getPhys req (pos / 16) * 16 + pos % 16 := by
          apply Int.add_nonneg
          · apply Int.mul_nonneg hphys (by decide)
          · exact hmod
        have hslot_lt : getPhys req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
          have h1 : getPhys req (pos / 16) * 16 < num_physical_blocks * 16 := by
            apply Int.mul_lt_mul_of_pos_right hphys_lt (by decide)
          have h2 : getPhys req (pos / 16) * 16 + pos % 16 < getPhys req (pos / 16) * 16 + 16 := by
            apply Int.add_lt_add_left hmod_lt
          have h3 : getPhys req (pos / 16) * 16 + 16 ≤ (getPhys req (pos / 16) + 1) * 16 := by
            simp [Int.add_mul]
          have h4 : (getPhys req (pos / 16) + 1) * 16 ≤ num_physical_blocks * 16 := by
            apply Int.mul_le_mul_of_nonneg_right (by linarith) (by decide)
          linarith
        exact Or.inr ⟨hslot, hslot_lt⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

end GlimmerVerify.Auto