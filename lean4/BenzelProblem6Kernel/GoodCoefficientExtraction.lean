import BenzelProblem6Kernel.GoodGeneratingSeries
import BenzelProblem6Kernel.DerivativeCoefficient

/-!
# Coefficient extraction from the evaluated Good series
-/

namespace BenzelProblem6Kernel

open PowerSeries

theorem coeff_totalGoodGeneratingSeries (degree : ℕ) :
    coeff ℚ degree totalGoodGeneratingSeries =
      ((degree + 6 : ℕ) : ℚ) / 3 *
        coeff ℚ degree (ternarySeries ^ 9) := by
  exact coefficient_of_derivative_form
    (ternarySeries ^ 9) totalGoodGeneratingSeries
    totalGoodGeneratingSeries_derivative_form degree

theorem coeff_totalGoodGeneratingSeries_closed (degree : ℕ) :
    coeff ℚ degree totalGoodGeneratingSeries =
      (3 * (degree + 6) : ℚ) / (2 * degree + 9) *
        (3 * degree + 8).choose degree := by
  rw [coeff_totalGoodGeneratingSeries,
    coeff_ternarySeries_pow_nine]
  push_cast
  ring

theorem coeff_totalGoodGeneratingSeries_ballot (degree : ℕ) :
    coeff ℚ degree totalGoodGeneratingSeries =
      2 * (3 * degree + 8).choose degree -
        choosePred (3 * degree + 8) degree := by
  rw [coeff_totalGoodGeneratingSeries_closed]
  exact (ballot_form_eq_closed_form degree).symm

end BenzelProblem6Kernel
