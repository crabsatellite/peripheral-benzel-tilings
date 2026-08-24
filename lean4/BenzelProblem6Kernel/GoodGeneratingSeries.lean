import BenzelProblem6Kernel.GoodJacobianSeries
import BenzelProblem6Kernel.TernaryDerivativeIdentity
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The rational generating series after Lagrange--Good evaluation
-/

namespace BenzelProblem6Kernel

open PowerSeries

noncomputable def goodLinearDenominator : ℚ⟦X⟧ :=
  C ℚ 3 - C ℚ 2 * ternarySeries

noncomputable def goodQuadraticDenominator : ℚ⟦X⟧ :=
  ternarySeries ^ 2 - C ℚ 3 * ternarySeries + C ℚ 3

theorem goodLinearDenominator_constantCoeff :
    constantCoeff ℚ goodLinearDenominator = 1 := by
  simp [goodLinearDenominator, ternarySeries_constantCoeff]
  norm_num

theorem goodQuadraticDenominator_constantCoeff :
    constantCoeff ℚ goodQuadraticDenominator = 1 := by
  simp [goodQuadraticDenominator, ternarySeries_constantCoeff]

theorem goodLinearDenominator_ne_zero :
    constantCoeff ℚ goodLinearDenominator ≠ 0 := by
  rw [goodLinearDenominator_constantCoeff]
  norm_num

theorem goodQuadraticDenominator_ne_zero :
    constantCoeff ℚ goodQuadraticDenominator ≠ 0 := by
  rw [goodQuadraticDenominator_constantCoeff]
  norm_num

noncomputable def positiveGoodGeneratingSeries : ℚ⟦X⟧ :=
  ternarySeries ^ 9 *
    (goodLinearDenominator * goodQuadraticDenominator)⁻¹

noncomputable def negativeGoodGeneratingSeries : ℚ⟦X⟧ :=
  (C ℚ 2 - ternarySeries) ^ 3 * positiveGoodGeneratingSeries

noncomputable def totalGoodGeneratingSeries : ℚ⟦X⟧ :=
  positiveGoodGeneratingSeries + negativeGoodGeneratingSeries

theorem good_chirality_factorization :
    1 + (C ℚ 2 - ternarySeries) ^ 3 =
      (C ℚ 3 - ternarySeries) * goodQuadraticDenominator := by
  simp only [goodQuadraticDenominator]
  have h2 : C ℚ (2 : ℚ) = (2 : ℚ⟦X⟧) := map_ofNat (C ℚ) 2
  have h3 : C ℚ (3 : ℚ) = (3 : ℚ⟦X⟧) := map_ofNat (C ℚ) 3
  rw [h2, h3]
  ring

theorem totalGoodGeneratingSeries_simplified :
    totalGoodGeneratingSeries =
      ternarySeries ^ 9 * (C ℚ 3 - ternarySeries) *
        goodLinearDenominator⁻¹ := by
  rw [totalGoodGeneratingSeries, negativeGoodGeneratingSeries,
    positiveGoodGeneratingSeries, PowerSeries.mul_inv_rev]
  have hcancel := PowerSeries.inv_mul_cancel goodQuadraticDenominator
    goodQuadraticDenominator_ne_zero
  calc
    ternarySeries ^ 9 *
          (goodQuadraticDenominator⁻¹ * goodLinearDenominator⁻¹) +
        (C ℚ 2 - ternarySeries) ^ 3 *
          (ternarySeries ^ 9 *
            (goodQuadraticDenominator⁻¹ * goodLinearDenominator⁻¹)) =
        ternarySeries ^ 9 *
          (1 + (C ℚ 2 - ternarySeries) ^ 3) *
          goodQuadraticDenominator⁻¹ * goodLinearDenominator⁻¹ := by ring
    _ = ternarySeries ^ 9 *
          ((C ℚ 3 - ternarySeries) * goodQuadraticDenominator) *
          goodQuadraticDenominator⁻¹ * goodLinearDenominator⁻¹ := by
      rw [good_chirality_factorization]
    _ = ternarySeries ^ 9 * (C ℚ 3 - ternarySeries) *
          goodLinearDenominator⁻¹ := by
      calc
        ternarySeries ^ 9 *
              ((C ℚ 3 - ternarySeries) * goodQuadraticDenominator) *
              goodQuadraticDenominator⁻¹ * goodLinearDenominator⁻¹ =
            ternarySeries ^ 9 * (C ℚ 3 - ternarySeries) *
              (goodQuadraticDenominator * goodQuadraticDenominator⁻¹) *
              goodLinearDenominator⁻¹ := by ring
        _ = _ := by
          rw [PowerSeries.mul_inv_cancel goodQuadraticDenominator
            goodQuadraticDenominator_ne_zero]
          ring

theorem ternarySeries_root_product :
    X * ternarySeries ^ 3 = ternarySeries - 1 := by
  have h := ternarySeries_equation
  linear_combination -h

theorem goodLinear_mul_powNineDerivative :
    goodLinearDenominator * d⁄dX ℚ (ternarySeries ^ 9) =
      C ℚ 9 * ternarySeries ^ 12 := by
  rw [ternarySeries_pow_nine_derivative]
  have hcleared := ternarySeries_derivative_cleared
  rw [goodLinearDenominator]
  change (C ℚ 3 - C ℚ 2 * ternarySeries) *
      (C ℚ 9 * ternarySeries ^ 8 * d⁄dX ℚ ternarySeries) = _
  rw [show (C ℚ 3 - C ℚ 2 * ternarySeries) *
      (C ℚ 9 * ternarySeries ^ 8 * d⁄dX ℚ ternarySeries) =
      C ℚ 9 * ternarySeries ^ 8 *
        ((C ℚ 3 - C ℚ 2 * ternarySeries) *
          d⁄dX ℚ ternarySeries) by ring,
    hcleared]
  ring

theorem totalGoodGeneratingSeries_derivative_form :
    totalGoodGeneratingSeries =
      C ℚ 2 * ternarySeries ^ 9 +
        C ℚ (1 / 3) * (X * d⁄dX ℚ (ternarySeries ^ 9)) := by
  rw [totalGoodGeneratingSeries_simplified]
  symm
  apply (PowerSeries.eq_mul_inv_iff_mul_eq
    goodLinearDenominator_ne_zero).2
  rw [show
      (C ℚ 2 * ternarySeries ^ 9 +
          C ℚ (1 / 3) * (X * d⁄dX ℚ (ternarySeries ^ 9))) *
          goodLinearDenominator =
        C ℚ 2 * ternarySeries ^ 9 * goodLinearDenominator +
          C ℚ (1 / 3) * X *
            (goodLinearDenominator * d⁄dX ℚ (ternarySeries ^ 9)) by ring,
    goodLinear_mul_powNineDerivative]
  have hroot := ternarySeries_root_product
  have h2 : C ℚ (2 : ℚ) = (2 : ℚ⟦X⟧) := map_ofNat (C ℚ) 2
  have h3 : C ℚ (3 : ℚ) = (3 : ℚ⟦X⟧) := map_ofNat (C ℚ) 3
  have hthirdNine : C ℚ (1 / 3 : ℚ) * C ℚ 9 = C ℚ 3 := by
    rw [← map_mul]
    norm_num
  rw [show C ℚ (1 / 3 : ℚ) * X *
      (C ℚ 9 * ternarySeries ^ 12) =
      C ℚ 3 * X * ternarySeries ^ 12 by
        rw [← hthirdNine]
        ring]
  rw [goodLinearDenominator, h2, h3]
  linear_combination 3 * ternarySeries ^ 9 * hroot

end BenzelProblem6Kernel
