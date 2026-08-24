import BenzelProblem6Kernel.BallotRecurrence
import BenzelProblem6Kernel.IndependentArmAlgebra
import Mathlib.Data.Fintype.Prod

/-!
# Fixed-sink arm carriers
-/

namespace BenzelProblem6Kernel

abbrev PositiveArmTriple (x y z : ℕ) :=
  RecursiveBallot (x + z + 1) (z + 1) ×
  RecursiveBallot (x + y + 1) (x + 1) ×
  RecursiveBallot (y + z + 1) (y + 1)

abbrev NegativeArmTriple (x y z : ℕ) :=
  RecursiveBallot (x + z + 2) z ×
  RecursiveBallot (x + y + 2) x ×
  RecursiveBallot (y + z + 2) y

theorem card_positiveArmTriple (x y z : ℕ) :
    Fintype.card (PositiveArmTriple x y z) = positiveChiralityCount x y z := by
  rw [Fintype.card_prod, Fintype.card_prod]
  rw [card_recursiveBallot_of_le (x + z + 1) (z + 1) (by omega)]
  rw [card_recursiveBallot_of_le (x + y + 1) (x + 1) (by omega)]
  rw [card_recursiveBallot_of_le (y + z + 1) (y + 1) (by omega)]
  have hz : x + z + 1 + (z + 1) = 2 * z + x + 2 := by omega
  have hx : x + y + 1 + (x + 1) = 2 * x + y + 2 := by omega
  have hy : y + z + 1 + (y + 1) = 2 * y + z + 2 := by omega
  rw [hz, hx, hy]
  simpa [ballotNumber, positiveArmTripleCount, positiveArmCount, mul_assoc] using
    positiveArmTripleCount_eq x y z

theorem card_negativeArmTriple (x y z : ℕ) :
    Fintype.card (NegativeArmTriple x y z) = negativeChiralityCount x y z := by
  rw [Fintype.card_prod, Fintype.card_prod]
  rw [card_recursiveBallot_of_le (x + z + 2) z (by omega)]
  rw [card_recursiveBallot_of_le (x + y + 2) x (by omega)]
  rw [card_recursiveBallot_of_le (y + z + 2) y (by omega)]
  have hz : x + z + 2 + z = 2 * z + x + 2 := by omega
  have hx : x + y + 2 + x = 2 * x + y + 2 := by omega
  have hy : y + z + 2 + y = 2 * y + z + 2 := by omega
  rw [hz, hx, hy]
  simp [negativeChiralityCount]
  ac_rfl

end BenzelProblem6Kernel
