import FiniteDefects.D4BallotFormulaInterface

/-! # Kernel producer for the exact d=4 cyclic ballot sum -/

namespace FiniteDefects

theorem d4BallotSumKernel : D4BallotSumEvidence where
  exact_count := d4TilingCount_ballot_formula
  ballot_zero := by
    intro x
    simp [d4R, ballotNumber]
  ballot_succ := by
    intro x y
    simp [d4R, ballotNumber]

end FiniteDefects
