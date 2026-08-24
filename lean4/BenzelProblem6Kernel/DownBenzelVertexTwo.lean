import BenzelProblem6Kernel.DownBenzelVertexOne

/-! # Residue-two down-vertex parameters -/

namespace BenzelProblem6Kernel

theorem downTwoParameter_anchor_mem (m : ℕ)
    (p : DownTwoParameter (m + 3)) :
    ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (downAnchorCell (downTwoParameterAnchor p) label) := by
  by_contra hnone
  simp only [not_exists] at hnone
  have hzero := hnone .zero
  have hone := hnone .one
  have htwo := hnone .two
  dsimp [inPeripheralBenzel, downAnchorCell,
    downTwoParameterAnchor, downTwoSimplexAnchor] at hzero hone htwo
  have hsum := p.1.sum_eq
  apply p.2
  simp only [downTwoExceptions, Finset.mem_insert,
    Finset.mem_singleton]
  have hcases :
      (p.1.u = 0 ∧ p.1.v = 0 ∧ p.1.w = m + 4) ∨
      (p.1.u = m + 4 ∧ p.1.v = 0 ∧ p.1.w = 0) := by
    omega
  rcases hcases with h | h
  · left
    apply simplexPoint_ext <;> simp [sourceOne] <;> omega
  · right
    apply simplexPoint_ext <;> simp [sourceTwo] <;> omega

end BenzelProblem6Kernel
