import GlimmerVerify.PagedKVProofs

namespace GlimmerVerify.Auto

def blockSize : Int := 16

/-- Model of the per-lane computation in `paged_kv_index_kernel`. -/
def kernelSlot
    (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (req pos : Int)
    (table : Int → Int → Int) : Int :=
  if req >= 0 && req < num_reqs && pos >= 0 then
    let logical_block : Int := pos / 16
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
    (num_reqs max_blocks_per_req num_physical_blocks : Int)
    (req pos : Int)
    (table : Int → Int → Int)
    (slot : Int)
    (hslot : slot = kernelSlot num_reqs max_blocks_per_req num_physical_blocks req pos table) :
    slot = -1 ∨ (0 ≤ slot ∧ slot < num_physical_blocks * 16) := by
  unfold kernelSlot at hslot
  split at hslot with hguard
  · -- guard fails
    simp [hguard] at hslot
    left
    exact hslot.symm
  · -- guard succeeds
    have hreq_ge : 0 ≤ req := by
      have := (and_assoc.mp (and_assoc.mp hguard)).1
      omega
    have hreq_lt : req < num_reqs := by
      have := (and_assoc.mp hguard).2.1
      omega
    have hpos_ge : 0 ≤ pos := by
      have := (and_assoc.mp hguard).2.2
      omega
    simp at hslot
    split at hslot with hlb
    · -- logical_block >= max_blocks_per_req
      simp [hlb] at hslot
      left
      exact hslot.symm
    · -- logical_block < max_blocks_per_req
      have hlb_lt : pos / 16 < max_blocks_per_req := hlb
      simp at hslot
      split at hslot with hphys
      · -- phys out of range
        simp [hphys] at hslot
        left
        exact hslot.symm
      · -- phys in range
        have hphys_ge : 0 ≤ (table req (pos / 16)) := by
          have := (and_assoc.mp hphys).1
          omega
        have hphys_lt : (table req (pos / 16)) < num_physical_blocks := by
          have := (and_assoc.mp hphys).2
          omega
        simp at hslot
        right
        constructor
        · -- 0 ≤ slot
          have hmod_ge : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
          have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
          have hphys_nonneg : 0 ≤ table req (pos / 16) := hphys_ge
          omega
        · -- slot < num_physical_blocks * 16
          have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
          have hphys_lt : (table req (pos / 16)) < num_physical_blocks := hphys_lt
          omega

end GlimmerVerify.Auto