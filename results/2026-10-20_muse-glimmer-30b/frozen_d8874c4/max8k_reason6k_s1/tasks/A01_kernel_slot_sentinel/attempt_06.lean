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
  by_cases h0 : req >= 0 && req < num_reqs && pos >= 0
  · have hreq_ge : req >= 0 := by
      have : (req >= 0) = true := by
        have := Int.and_eq_true_iff.mp (by
          have : (req >= 0 && req < num_reqs && pos >= 0) = true := h0
          simpa using this)
        exact this.1
      simpa using this
    have hreq_lt : req < num_reqs := by
      have : (req < num_reqs) = true := by
        have := Int.and_eq_true_iff.mp (by
          have : (req >= 0 && req < num_reqs && pos >= 0) = true := h0
          simpa using this)
        exact this.2.1
      simpa using this
    have hpos_ge : pos >= 0 := by
      have : (pos >= 0) = true := by
        have := Int.and_eq_true_iff.mp (by
          have : (req >= 0 && req < num_reqs && pos >= 0) = true := h0
          simpa using this)
        exact this.2.2
      simpa using this
    let logical_block : Int := pos / 16
    by_cases h1 : logical_block < max_blocks_per_req
    · let phys : Int := table req logical_block
      by_cases h2 : phys >= 0 && phys < num_physical_blocks
      · have hphys_ge : phys >= 0 := by
          have := Int.and_eq_true_iff.mp h2
          exact this.1
        have hphys_lt : phys < num_physical_blocks := by
          have := Int.and_eq_true_iff.mp h2
          exact this.2
        simp [h0, h1, h2]
        have hmod_nonneg : 0 ≤ pos % 16 := Int.emod_nonneg pos 16
        have hmod_lt : pos % 16 < 16 := Int.emod_lt_of_pos pos (by decide : (0: Int) < 16)
        right
        constructor
        · omega
        · omega
      · simp [h0, h1, h2]
        left
        rfl
    · simp [h0, h1]
      left
      rfl
  · simp [h0]
    left
    rfl

end GlimmerVerify.Auto