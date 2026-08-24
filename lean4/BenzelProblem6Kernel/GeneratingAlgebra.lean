import BenzelProblem6Kernel.ChiralityCounts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebraic endpoint identities

The formal-power-series constant-term producer is not yet implemented here.
This file records and proves the rational identities used after that producer.
-/

namespace BenzelProblem6Kernel

theorem chirality_rational_factorization (T : ℚ) :
    1 + (2 - T) ^ 3 = (3 - T) * (T ^ 2 - 3 * T + 3) := by
  ring

theorem jacobian_difference_of_cubes (T : ℚ) (hT : T ≠ 0) :
    ((2 - T) / T) ^ 3 - ((T - 1) / T) ^ 3 =
      ((3 - 2 * T) * (T ^ 2 - 3 * T + 3)) / T ^ 3 := by
  field_simp
  ring

theorem total_generating_rational_simplification
    (T : ℚ) (h1 : 3 - 2 * T ≠ 0) (h2 : T ^ 2 - 3 * T + 3 ≠ 0) :
    T ^ 9 / ((3 - 2 * T) * (T ^ 2 - 3 * T + 3)) +
        (2 - T) ^ 3 * (T ^ 9 / ((3 - 2 * T) * (T ^ 2 - 3 * T + 3))) =
      T ^ 9 * (3 - T) / (3 - 2 * T) := by
  field_simp [h1, h2]
  ring

end BenzelProblem6Kernel
