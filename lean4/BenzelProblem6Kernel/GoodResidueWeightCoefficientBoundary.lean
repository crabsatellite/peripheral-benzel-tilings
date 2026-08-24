import BenzelProblem6Kernel.GoodResidueWeightCoefficientPositive

/-!
# Boundary-index coefficients of the Good residue weight
-/

namespace BenzelProblem6Kernel

open MvPowerSeries

theorem coeff_goodResidueWeight_zero_a (y z : ℕ) :
    coeff ℚ (goodMultiIndex 0 (y + 1) (z + 1))
        (goodResidueWeight 0 (y + 1) (z + 1)) =
      goodDeterminantCoefficient 0 (y + 1) (z + 1) := by
  rw [goodResidueWeight_factorization_of_axis_positive _ _ _
    (by omega) (by omega) (by omega)]
  let powerA := 2 * 0 + (y + 1) - 1
  let powerB := 2 * (y + 1) + (z + 1) - 1
  let powerC := 2 * (z + 1) + 0 - 1
  let separated : GoodMvSeries :=
    (1 + X goodVarA) ^ powerA *
      (1 + X goodVarB) ^ powerB *
      (1 + X goodVarC) ^ powerC
  rw [show goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * 0 + (y + 1) - 1) *
        (1 + X goodVarB) ^ (2 * (y + 1) + (z + 1) - 1) *
        (1 + X goodVarC) ^ (2 * (z + 1) + 0 - 1) =
      goodJacobianNumeratorMv * separated by
        dsimp [separated, powerA, powerB, powerC]
        ring]
  change coeff ℚ (goodMultiIndex 0 (y + 1) (z + 1))
      (goodJacobianNumeratorMv * separated) = _
  have hexpand : goodJacobianNumeratorMv * separated =
      separated - X goodVarA * separated - X goodVarB * separated -
          X goodVarC * separated +
        X goodVarA * X goodVarB * separated +
        X goodVarA * X goodVarC * separated +
        X goodVarB * X goodVarC * separated -
        2 * (X goodVarA * X goodVarB * X goodVarC * separated) := by
    simp only [goodJacobianNumeratorMv]
    ring
  have hXa : coeff ℚ (goodMultiIndex 0 (y + 1) (z + 1))
      (X goodVarA * separated) = 0 := coeff_X_mul_good_zero _ _ _
  have hXaXb : coeff ℚ (goodMultiIndex 0 (y + 1) (z + 1))
      (X goodVarA * X goodVarB * separated) = 0 := by
    rw [show X goodVarA * X goodVarB * separated =
      X goodVarA * (X goodVarB * separated) by ring,
      coeff_X_mul_good_zero]
  have hXaXc : coeff ℚ (goodMultiIndex 0 (y + 1) (z + 1))
      (X goodVarA * X goodVarC * separated) = 0 := by
    rw [show X goodVarA * X goodVarC * separated =
      X goodVarA * (X goodVarC * separated) by ring,
      coeff_X_mul_good_zero]
  have hXaXbXc : coeff ℚ (goodMultiIndex 0 (y + 1) (z + 1))
      (X goodVarA * X goodVarB * X goodVarC * separated) = 0 := by
    rw [show X goodVarA * X goodVarB * X goodVarC * separated =
      X goodVarA * (X goodVarB * X goodVarC * separated) by ring,
      coeff_X_mul_good_zero]
  rw [hexpand]
  have htwo : (2 : GoodMvSeries) = C GoodVariable ℚ 2 :=
    (map_ofNat (C GoodVariable ℚ) 2).symm
  rw [htwo]
  simp only [map_sub, map_add, MvPowerSeries.coeff_C_mul,
    hXa, hXaXb, hXaXc, hXaXbXc, sub_zero, add_zero, zero_mul,
    coeff_X_mul_good_succ_b, coeff_X_mul_good_succ_c,
    coeff_XbXc_mul_good_succ]
  rw [show coeff ℚ (goodMultiIndex 0 (y + 1) (z + 1)) separated =
      ((powerA.choose 0 : ℚ) * powerB.choose (y + 1) *
        powerC.choose (z + 1)) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex 0 y (z + 1)) separated =
      ((powerA.choose 0 : ℚ) * powerB.choose y *
        powerC.choose (z + 1)) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex 0 (y + 1) z) separated =
      ((powerA.choose 0 : ℚ) * powerB.choose (y + 1) *
        powerC.choose z) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex 0 y z) separated =
      ((powerA.choose 0 : ℚ) * powerB.choose y * powerC.choose z) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [goodDeterminantCoefficient]
  simp only [goodDifferenceCoefficient_zero,
    goodPreviousCoefficient_zero, zero_mul, sub_zero,
    goodDifferenceCoefficient, goodMainCoefficient,
    goodPreviousCoefficient, goodReducedTop_succ,
    goodReducedTop_succ_zero, choosePred]
  dsimp [powerA, powerB, powerC]
  simp
  ring

end BenzelProblem6Kernel
