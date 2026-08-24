import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring

/-!
# Coefficient extraction from the derivative form
-/

namespace BenzelProblem6Kernel

open PowerSeries

theorem coeff_X_mul_derivative {R : Type*} [CommSemiring R]
    (series : R⟦X⟧) (degree : ℕ) :
    coeff R degree (X * (d⁄dX R series)) =
      coeff R degree series * degree := by
  cases degree with
  | zero => simp
  | succ degree =>
      rw [show (X : R⟦X⟧) = X ^ 1 by simp]
      rw [coeff_X_pow_mul]
      rw [coeff_derivative]
      simp [Nat.cast_add, Nat.cast_one]

theorem coefficient_of_derivative_form
    (series total : ℚ⟦X⟧)
    (hform : total = C ℚ 2 * series +
      C ℚ (1 / 3) * (X * (d⁄dX ℚ series)))
    (degree : ℕ) :
    coeff ℚ degree total =
      ((degree + 6 : ℕ) : ℚ) / 3 * coeff ℚ degree series := by
  rw [hform]
  rw [map_add, coeff_C_mul, coeff_C_mul, coeff_X_mul_derivative]
  push_cast
  ring

end BenzelProblem6Kernel
