import BenzelProblem6Kernel.GoodResidueWeightPositive

/-!
# Positive-index coefficient of the Good residue weight
-/

namespace BenzelProblem6Kernel

open MvPowerSeries

theorem goodReducedTop_succ (majority adjacent : ℕ) :
    goodReducedTop (majority + 1) (adjacent + 1) =
      2 * (majority + 1) + (adjacent + 1) - 1 := by
  simp [goodReducedTop]

theorem goodReducedTop_succ_zero (majority : ℕ) :
    goodReducedTop (majority + 1) 0 = 2 * (majority + 1) - 1 := by
  simp [goodReducedTop]

theorem coeff_goodResidueWeight_positive (x y z : ℕ) :
    coeff ℚ (goodMultiIndex (x + 1) (y + 1) (z + 1))
        (goodResidueWeight (x + 1) (y + 1) (z + 1)) =
      goodDeterminantCoefficient (x + 1) (y + 1) (z + 1) := by
  rw [goodResidueWeight_positive_factorization _ _ _
    (by omega) (by omega) (by omega)]
  let powerA := 2 * (x + 1) + (y + 1) - 1
  let powerB := 2 * (y + 1) + (z + 1) - 1
  let powerC := 2 * (z + 1) + (x + 1) - 1
  let separated : GoodMvSeries :=
    (1 + X goodVarA) ^ powerA *
      (1 + X goodVarB) ^ powerB *
      (1 + X goodVarC) ^ powerC
  rw [show goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * (x + 1) + (y + 1) - 1) *
        (1 + X goodVarB) ^ (2 * (y + 1) + (z + 1) - 1) *
        (1 + X goodVarC) ^ (2 * (z + 1) + (x + 1) - 1) =
      goodJacobianNumeratorMv * separated by
        dsimp [separated, powerA, powerB, powerC]
        ring]
  change coeff ℚ (goodMultiIndex (x + 1) (y + 1) (z + 1))
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
  rw [hexpand]
  have htwo : (2 : GoodMvSeries) = C GoodVariable ℚ 2 := by
    exact (map_ofNat (C GoodVariable ℚ) 2).symm
  rw [htwo]
  simp only [map_sub, map_add, MvPowerSeries.coeff_C_mul,
    coeff_X_mul_good_succ,
    coeff_X_mul_good_succ_b, coeff_X_mul_good_succ_c,
    coeff_XaXb_mul_good_succ, coeff_XaXc_mul_good_succ,
    coeff_XbXc_mul_good_succ, coeff_XaXbXc_mul_good_succ]
  rw [show coeff ℚ (goodMultiIndex (x + 1) (y + 1) (z + 1)) separated =
      ((powerA.choose (x + 1) : ℚ) * powerB.choose (y + 1) *
        powerC.choose (z + 1)) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x (y + 1) (z + 1)) separated =
      ((powerA.choose x : ℚ) * powerB.choose (y + 1) *
        powerC.choose (z + 1)) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex (x + 1) y (z + 1)) separated =
      ((powerA.choose (x + 1) : ℚ) * powerB.choose y *
        powerC.choose (z + 1)) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex (x + 1) (y + 1) z) separated =
      ((powerA.choose (x + 1) : ℚ) * powerB.choose (y + 1) *
        powerC.choose z) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y (z + 1)) separated =
      ((powerA.choose x : ℚ) * powerB.choose y *
        powerC.choose (z + 1)) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x (y + 1) z) separated =
      ((powerA.choose x : ℚ) * powerB.choose (y + 1) *
        powerC.choose z) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex (x + 1) y z) separated =
      ((powerA.choose (x + 1) : ℚ) * powerB.choose y *
        powerC.choose z) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z) separated =
      ((powerA.choose x : ℚ) * powerB.choose y * powerC.choose z) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [goodDeterminantCoefficient]
  simp only [goodDifferenceCoefficient, goodMainCoefficient,
    goodPreviousCoefficient, goodReducedTop_succ, choosePred]
  dsimp [powerA, powerB, powerC]
  ring

theorem coeff_goodResidueWeight_of_axis_positive
    (x y z : ℕ)
    (hApos : 0 < 2 * x + y) (hBpos : 0 < 2 * y + z)
    (hCpos : 0 < 2 * z + x) :
    coeff ℚ (goodMultiIndex x y z) (goodResidueWeight x y z) =
      goodDeterminantCoefficient x y z := by
  rw [goodResidueWeight_factorization_of_axis_positive
    x y z hApos hBpos hCpos]
  let powerA := 2 * x + y - 1
  let powerB := 2 * y + z - 1
  let powerC := 2 * z + x - 1
  let separated : GoodMvSeries :=
    (1 + X goodVarA) ^ powerA *
      (1 + X goodVarB) ^ powerB *
      (1 + X goodVarC) ^ powerC
  rw [show goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * x + y - 1) *
        (1 + X goodVarB) ^ (2 * y + z - 1) *
        (1 + X goodVarC) ^ (2 * z + x - 1) =
      goodJacobianNumeratorMv * separated by
        dsimp [separated, powerA, powerB, powerC]
        ring]
  change coeff ℚ (goodMultiIndex x y z)
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
  rw [hexpand]
  have htwo : (2 : GoodMvSeries) = C GoodVariable ℚ 2 :=
    (map_ofNat (C GoodVariable ℚ) 2).symm
  rw [htwo]
  simp only [map_sub, map_add, MvPowerSeries.coeff_C_mul]
  rw [show coeff ℚ (goodMultiIndex x y z) separated =
      ((powerA.choose x : ℚ) * powerB.choose y * powerC.choose z) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z) (X goodVarA * separated) =
      ((choosePred powerA x : ℕ) : ℚ) * powerB.choose y *
        powerC.choose z by
        exact coeff_Xa_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z) (X goodVarB * separated) =
      ((powerA.choose x : ℚ) * choosePred powerB y *
        powerC.choose z) by
        exact coeff_Xb_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z) (X goodVarC * separated) =
      ((powerA.choose x : ℚ) * powerB.choose y *
        choosePred powerC z) by
        exact coeff_Xc_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z)
      (X goodVarA * X goodVarB * separated) =
      ((choosePred powerA x : ℕ) : ℚ) * choosePred powerB y *
        powerC.choose z by
        exact coeff_XaXb_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z)
      (X goodVarA * X goodVarC * separated) =
      ((choosePred powerA x : ℕ) : ℚ) * powerB.choose y *
        choosePred powerC z by
        exact coeff_XaXc_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z)
      (X goodVarB * X goodVarC * separated) =
      ((powerA.choose x : ℚ) * choosePred powerB y *
        choosePred powerC z) by
        exact coeff_XbXc_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex x y z)
      (X goodVarA * X goodVarB * X goodVarC * separated) =
      ((choosePred powerA x : ℕ) : ℚ) * choosePred powerB y *
        choosePred powerC z by
        exact coeff_XaXbXc_separated_good_powers _ _ _ _ _ _]
  rw [goodDeterminantCoefficient]
  simp only [goodDifferenceCoefficient, goodMainCoefficient,
    goodPreviousCoefficient]
  have htopA : goodReducedTop x y = powerA := by
    dsimp [goodReducedTop, powerA]
  have htopB : goodReducedTop y z = powerB := by
    dsimp [goodReducedTop, powerB]
  have htopC : goodReducedTop z x = powerC := by
    dsimp [goodReducedTop, powerC]
  rw [htopA, htopB, htopC]
  ring

end BenzelProblem6Kernel
