import BenzelProblem6Kernel.TernaryLagrangeCoefficient
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Derivative form of the ternary generating series
-/

namespace BenzelProblem6Kernel

open PowerSeries

theorem ternarySeries_derivative_equation :
    d⁄dX ℚ ternarySeries =
      ternarySeries ^ 3 + C ℚ 3 * X * ternarySeries ^ 2 *
        d⁄dX ℚ ternarySeries := by
  have h := congrArg (d⁄dX ℚ) ternarySeries_equation
  rw [map_add, (d⁄dX ℚ).map_one_eq_zero, (d⁄dX ℚ).leibniz,
    derivative_X, (d⁄dX ℚ).leibniz_pow] at h
  have h3 : C ℚ (3 : ℚ) = (3 : ℚ⟦X⟧) := map_ofNat (C ℚ) 3
  rw [h3]
  simp only [nsmul_eq_mul, smul_eq_mul, zero_add] at h
  linear_combination h

theorem ternarySeries_derivative_cleared :
    (C ℚ 3 - C ℚ 2 * ternarySeries) *
        d⁄dX ℚ ternarySeries = ternarySeries ^ 4 := by
  have hequation := ternarySeries_derivative_equation
  have hroot := ternarySeries_equation
  have h3 : C ℚ (3 : ℚ) = (3 : ℚ⟦X⟧) := map_ofNat (C ℚ) 3
  rw [h3] at hequation
  change ((3 : ℚ⟦X⟧) - 2 * ternarySeries) *
      d⁄dX ℚ ternarySeries = ternarySeries ^ 4
  linear_combination ternarySeries * hequation -
    3 * (d⁄dX ℚ ternarySeries) * hroot

theorem ternarySeries_pow_nine_derivative :
    d⁄dX ℚ (ternarySeries ^ 9) =
      C ℚ 9 * ternarySeries ^ 8 * d⁄dX ℚ ternarySeries := by
  have h9 : C ℚ (9 : ℚ) = (9 : ℚ⟦X⟧) := map_ofNat (C ℚ) 9
  rw [h9]
  rw [(d⁄dX ℚ).leibniz_pow]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

end BenzelProblem6Kernel
