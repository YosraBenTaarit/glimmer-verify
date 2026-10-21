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
  by_cases hguard : req >= 0 && req < num_reqs && pos >= 0
  · by_cases hlb : pos / 16 < max_blocks_per_req
    · by_cases hphys : table req (pos / 16) >= 0 && table req (pos / 16) < num_physical_blocks
      · have h_eq : slot = table req (pos / 16) * 16 + pos % 16 := by
          simp [hguard, hlb, hphys] at hslot
          exact hslot
        rw [h_eq]
        have hpos : 0 ≤ pos := by
          have h1 : req >= 0 := by
            have : req >= 0 ∧ req < num_reqs ∧ pos >= 0 := by
              constructor
              · exact (Int.and_imp.mp hguard).1
              · constructor
                · exact (Int.and_imp.mp ((Int.and_imp.mp hguard).2)).1
                · exact (Int.and_imp.mp ((Int.and_imp.mp hguard).2)).2
            exact this.1
          have h2 : req < num_reqs := by
            have : req >= 0 ∧ req < num_reqs ∧ pos >= 0 := by
              constructor
              · exact (Int.and_imp.mp hguard).1
              · constructor
                · exact (Int.and_imp.mp ((Int.and_imp.mp hguard).2)).1
                · exact (Int.and_imp.mp ((Int.and_imp.mp hguard).2)).2
            exact this.2.1
          have h3 : pos >= 0 := by
            have : req >= 0 ∧ req < num_reqs ∧ pos >= 0 := by
              constructor
              · exact (Int.and_imp.mp hguard).1
              · constructor
                · exact (Int.and_imp.mp ((Int.and_imp.mp hguard).2)).1
                · exact (Int.and_imp.mp ((Int.and_imp.mp hguard).2)).2
            exact this.2.2
          exact h3
        have hphys_ge : 0 ≤ table req (pos / 16) := by
          have h1 : table req (pos / 16) >= 0 := by
            have : table req (pos / 16) >= 0 ∧ table req (pos / 16) < num_physical_blocks := by
              constructor
              · exact (Int.and_imp.mp hphys).1
              · exact (Int.and_imp.mp hphys).2
            exact this.1
          exact h1
        have hphys_lt : table req (pos / 16) < num_physical_blocks := by
          have : table req (pos / 16) >= 0 ∧ table req (pos / 16) < num_physical_blocks := by
            constructor
            · exact (Int.and_imp.mp hphys).1
            · exact (Int.and_imp.mp hphys).2
          exact this.2
        have hmod_nonneg : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide)
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
        have hslot_ge : 0 ≤ table req (pos / 16) * 16 + pos % 16 := by
          have h1 : 0 ≤ table req (pos / 16) * 16 := Int.mul_nonneg hphys_ge (by decide)
          omega
        have hslot_lt : table req (pos / 16) * 16 + pos % 16 < num_physical_blocks * 16 := by
          have h1 : table req (pos / 16) * 16 < num_physical_blocks * 16 :=
            Int.mul_lt_mul_of_pos_right hphys_lt (by decide)
          omega
        right
        exact ⟨hslot_ge, hslot_lt⟩
      · have h_eq : slot = -1 := by
          simp [hguard, hlb, hphys] at hslot
          exact hslot
        rw [h_eq]
        left; rfl
    · have h_eq : slot = -1 := by
        simp [hguard, hlb] at hslot
        exact hslot
      rw [h_eq]
      left; rfl
  · have h_eq : slot = -1 := by
      simp [hguard] at hslot
      exact hslot
    rw [h_eq]
    left; rfl

end GlimmerVerify.Auto