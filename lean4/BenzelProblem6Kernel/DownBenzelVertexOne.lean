import BenzelProblem6Kernel.DownBenzelVertexZero

/-! # Residue-one down-vertex parameters -/

namespace BenzelProblem6Kernel

theorem downOneParameter_anchor_mem (m : ℕ)
    (p : DownOneParameter (m + 3)) :
    ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (downAnchorCell (downOneParameterAnchor p) label) := by
  by_contra hnone
  simp only [not_exists] at hnone
  have hzero := hnone .zero
  have hone := hnone .one
  have htwo := hnone .two
  dsimp [inPeripheralBenzel, downAnchorCell,
    downOneParameterAnchor, downOneSimplexAnchor,
    simplexAnchor] at hzero hone htwo
  have hsum := p.1.sum_eq
  apply p.2
  simp only [downOneExceptions, Finset.mem_insert,
    Finset.mem_singleton]
  have hcases :
      (p.1.u = 0 ∧ p.1.v = m + 4 ∧ p.1.w = 0) ∨
      (p.1.u = m + 4 ∧ p.1.v = 0 ∧ p.1.w = 0) := by
    omega
  rcases hcases with h | h
  · left
    apply simplexPoint_ext <;> simp [sourceZero] <;> omega
  · right
    apply simplexPoint_ext <;> simp [sourceTwo] <;> omega

end BenzelProblem6Kernel
