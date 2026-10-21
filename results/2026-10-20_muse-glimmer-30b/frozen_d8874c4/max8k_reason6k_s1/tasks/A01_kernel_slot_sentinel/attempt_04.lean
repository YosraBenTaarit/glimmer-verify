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
  by_cases hreq_ge : req >= 0
  · by_cases hreq_lt : req < num_reqs
    · by_cases hpos_ge : pos >= 0
      · simp [hreq_ge, hreq_lt, hpos_ge]
        let logical_block : Int := pos / 16
        by_cases hlb : logical_block < max_blocks_per_req
        · simp [hlb]
          let phys : Int := table req logical_block
          by_cases hphys_ge : phys >= 0
          · by_cases hphys_lt : phys < num_physical_blocks
            · simp [hphys_ge, hphys_lt]
              have hmod_nonneg : 0 ≤ pos % 16 := Int.emod_nonneg pos (by decide : (0: Int) < 16)
              have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide : (0: Int) < 16)
              right
              constructor
              · omega
              · omega
            · simp [hphys_ge, hphys_lt]
              left
              rfl
          · simp [hphys_ge]
            left
            rfl
        · simp [hlb]
          left
          rfl
      · simp [hreq_ge, hreq_lt, hpos_ge]
        left
        rfl
    · simp [hreq_ge, hreq_lt]
      left
      rfl
  · simp [hreq_ge]
    left
    rfl

end GlimmerVerify.Auto