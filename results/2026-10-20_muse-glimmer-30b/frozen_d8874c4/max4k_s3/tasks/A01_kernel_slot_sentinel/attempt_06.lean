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
  by_cases h1 : req ≥ 0 ∧ req < num_reqs ∧ pos ≥ 0
  · by_cases h2 : pos / 16 < max_blocks_per_req
    · by_cases h3 : getPhys req (pos / 16) ≥ 0 ∧ getPhys req (pos / 16) < num_physical_blocks
      · simp [h1, h2, h3]
        right
        have hmod_nonneg : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide)
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide)
        have hphys_nonneg : 0 ≤ getPhys req (pos / 16) := (h3).1
        have hphys_lt : getPhys req (pos / 16) < num_physical_blocks := (h3).2
        omega
      · simp [h1, h2, h3]
      · simp [h1, h2]
  · simp [h1]

end GlimmerVerify.Auto