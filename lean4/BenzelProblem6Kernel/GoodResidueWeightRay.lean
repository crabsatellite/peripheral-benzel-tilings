import BenzelProblem6Kernel.GoodResidueWeightCoefficientPositive

/-!
# Axis-ray coefficients of the Good residue weight
-/

namespace BenzelProblem6Kernel

open MvPowerSeries

theorem goodResidueWeight_ray_a_factorization (x : ℕ) :
    goodResidueWeight (x + 1) 0 0 =
      goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * x + 1) *
        (1 + X goodVarC) ^ x *
        (1 + X goodVarB)⁻¹ := by
  have hInvA := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarA : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarA)
  have hInvC := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarC : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarC)
  rw [goodResidueWeight, goodJacobianDetMv,
    goodJacobianDenominatorMv]
  rw [show goodJacobianNumeratorMv *
      ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
      goodPhiA ^ (x + 1) * goodPhiB ^ 0 * goodPhiC ^ 0 =
      goodJacobianNumeratorMv *
        ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
        (goodPhiA ^ (x + 1) * goodPhiB ^ 0 * goodPhiC ^ 0) by ring,
    goodPhiPowers_factorization,
    MvPowerSeries.mul_inv_rev, MvPowerSeries.mul_inv_rev]
  simp only [mul_zero, zero_add, pow_zero, mul_one]
  have hPowA : ((1 + X goodVarA : GoodMvSeries) ^ (2 * (x + 1))) =
      (1 + X goodVarA) ^ (2 * x + 1) * (1 + X goodVarA) := by
    rw [show 2 * (x + 1) = (2 * x + 1) + 1 by omega, pow_succ]
  have hPowC : ((1 + X goodVarC : GoodMvSeries) ^ (x + 1)) =
      (1 + X goodVarC) ^ x * (1 + X goodVarC) := by rw [pow_succ]
  rw [show 2 * (x + 1) + 0 = 2 * (x + 1) by omega,
    hPowA, hPowC]
  rw [show goodJacobianNumeratorMv *
        ((1 + X goodVarC)⁻¹ *
          ((1 + X goodVarB)⁻¹ * (1 + X goodVarA)⁻¹)) *
        (((1 + X goodVarA) ^ (2 * x + 1) * (1 + X goodVarA)) *
          ((1 + X goodVarC) ^ x * (1 + X goodVarC))) =
      goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * x + 1) *
        (1 + X goodVarC) ^ x *
        (1 + X goodVarB)⁻¹ *
        ((1 + X goodVarA) * (1 + X goodVarA)⁻¹) *
        ((1 + X goodVarC) * (1 + X goodVarC)⁻¹) by ring,
    hInvA, hInvC]
  ring

theorem coeff_goodResidueWeight_ray_a (x : ℕ) :
    coeff ℚ (goodMultiIndex (x + 1) 0 0)
        (goodResidueWeight (x + 1) 0 0) = 0 := by
  rw [goodResidueWeight_ray_a_factorization]
  let core : GoodMvSeries :=
    goodJacobianNumeratorMv * (1 + X goodVarA) ^ (2 * x + 1) *
      (1 + X goodVarC) ^ x
  change coeff ℚ (goodMultiIndex (x + 1) 0 0)
      (core * (1 + X goodVarB)⁻¹) = 0
  have hInvB := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarB : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarB)
  have hInvBform : ((1 + X goodVarB : GoodMvSeries)⁻¹) =
      1 - X goodVarB * (1 + X goodVarB)⁻¹ := by
    have := hInvB
    linear_combination this
  rw [hInvBform]
  rw [show core * (1 - X goodVarB * (1 + X goodVarB)⁻¹) =
      core - X goodVarB * (core * (1 + X goodVarB)⁻¹) by ring,
    map_sub, coeff_X_mul_good_zero_b, sub_zero]
  have hnum : goodJacobianNumeratorMv =
      ((1 : GoodMvSeries) - X goodVarA) *
          ((1 : GoodMvSeries) - X goodVarC) +
        X goodVarB *
          (-((1 : GoodMvSeries) - X goodVarA) *
              ((1 : GoodMvSeries) - X goodVarC) -
            X goodVarA * X goodVarC) := by
    simp only [goodJacobianNumeratorMv]
    ring
  dsimp [core]
  rw [hnum]
  rw [show (((1 : GoodMvSeries) - X goodVarA) *
          ((1 : GoodMvSeries) - X goodVarC) +
        X goodVarB *
          (-((1 : GoodMvSeries) - X goodVarA) *
              ((1 : GoodMvSeries) - X goodVarC) -
            X goodVarA * X goodVarC)) *
        (1 + X goodVarA) ^ (2 * x + 1) *
        (1 + X goodVarC) ^ x =
      ((1 : GoodMvSeries) - X goodVarA) *
          ((1 : GoodMvSeries) - X goodVarC) *
          ((1 + X goodVarA) ^ (2 * x + 1) *
            (1 + X goodVarC) ^ x) +
        X goodVarB *
          ((-((1 : GoodMvSeries) - X goodVarA) *
              ((1 : GoodMvSeries) - X goodVarC) -
            X goodVarA * X goodVarC) *
            (1 + X goodVarA) ^ (2 * x + 1) *
            (1 + X goodVarC) ^ x) by ring,
    map_add, coeff_X_mul_good_zero_b, add_zero]
  let separated : GoodMvSeries :=
    (1 + X goodVarA) ^ (2 * x + 1) *
      (1 + X goodVarB) ^ 0 * (1 + X goodVarC) ^ x
  rw [show ((1 : GoodMvSeries) - X goodVarA) *
        ((1 : GoodMvSeries) - X goodVarC) *
        ((1 + X goodVarA) ^ (2 * x + 1) *
          (1 + X goodVarC) ^ x) =
      separated - X goodVarA * separated - X goodVarC * separated +
        X goodVarA * X goodVarC * separated by
          dsimp [separated]
          ring,
    map_add, map_sub]
  simp only [map_sub]
  rw [show coeff ℚ (goodMultiIndex (x + 1) 0 0) separated =
      (((2 * x + 1).choose (x + 1) : ℕ) : ℚ) by
        simpa [separated] using
          coeff_separated_good_powers (2 * x + 1) 0 x (x + 1) 0 0]
  rw [show coeff ℚ (goodMultiIndex (x + 1) 0 0)
      (X goodVarA * separated) =
      (((2 * x + 1).choose x : ℕ) : ℚ) by
        simpa [separated, choosePred] using
          coeff_Xa_separated_good_powers (2 * x + 1) 0 x (x + 1) 0 0]
  rw [coeff_X_mul_good_zero_c]
  have hXaXc : coeff ℚ (goodMultiIndex (x + 1) 0 0)
      (X goodVarA * X goodVarC * separated) = 0 := by
    apply (MvPowerSeries.X_dvd_iff (s := goodVarC)).mp
      ⟨X goodVarA * separated, by ring⟩
    simp
  rw [hXaXc]
  simp
  rw [Nat.choose_symm_half]
  ring

theorem goodResidueWeight_ray_b_factorization (y : ℕ) :
    goodResidueWeight 0 (y + 1) 0 =
      goodJacobianNumeratorMv *
        (1 + X goodVarB) ^ (2 * y + 1) *
        (1 + X goodVarA) ^ y *
        (1 + X goodVarC)⁻¹ := by
  have hInvA := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarB : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarB)
  have hInvC := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarA : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarA)
  rw [goodResidueWeight, goodJacobianDetMv,
    goodJacobianDenominatorMv]
  rw [show goodJacobianNumeratorMv *
      ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
      goodPhiA ^ 0 * goodPhiB ^ (y + 1) * goodPhiC ^ 0 =
      goodJacobianNumeratorMv *
        ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
        (goodPhiA ^ 0 * goodPhiB ^ (y + 1) * goodPhiC ^ 0) by ring,
    goodPhiPowers_factorization,
    MvPowerSeries.mul_inv_rev, MvPowerSeries.mul_inv_rev]
  simp only [mul_zero, zero_add, pow_zero, mul_one]
  have hPowA : ((1 + X goodVarB : GoodMvSeries) ^ (2 * (y + 1))) =
      (1 + X goodVarB) ^ (2 * y + 1) * (1 + X goodVarB) := by
    rw [show 2 * (y + 1) = (2 * y + 1) + 1 by omega, pow_succ]
  have hPowC : ((1 + X goodVarA : GoodMvSeries) ^ (y + 1)) =
      (1 + X goodVarA) ^ y * (1 + X goodVarA) := by rw [pow_succ]
  rw [show 2 * (y + 1) + 0 = 2 * (y + 1) by omega,
    hPowA, hPowC]
  rw [show goodJacobianNumeratorMv *
        ((1 + X goodVarC)⁻¹ *
          ((1 + X goodVarB)⁻¹ * (1 + X goodVarA)⁻¹)) *
        (((1 + X goodVarA) ^ y * (1 + X goodVarA)) *
          ((1 + X goodVarB) ^ (2 * y + 1) * (1 + X goodVarB))) =
      goodJacobianNumeratorMv *
        (1 + X goodVarB) ^ (2 * y + 1) *
        (1 + X goodVarA) ^ y *
        (1 + X goodVarC)⁻¹ *
        ((1 + X goodVarB) * (1 + X goodVarB)⁻¹) *
        ((1 + X goodVarA) * (1 + X goodVarA)⁻¹) by ring,
    hInvA, hInvC]
  ring

theorem coeff_goodResidueWeight_ray_b (y : ℕ) :
    coeff ℚ (goodMultiIndex 0 (y + 1) 0)
        (goodResidueWeight 0 (y + 1) 0) = 0 := by
  rw [goodResidueWeight_ray_b_factorization]
  let core : GoodMvSeries :=
    goodJacobianNumeratorMv * (1 + X goodVarB) ^ (2 * y + 1) *
      (1 + X goodVarA) ^ y
  change coeff ℚ (goodMultiIndex 0 (y + 1) 0)
      (core * (1 + X goodVarC)⁻¹) = 0
  have hInvB := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarC : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarC)
  have hInvBform : ((1 + X goodVarC : GoodMvSeries)⁻¹) =
      1 - X goodVarC * (1 + X goodVarC)⁻¹ := by
    have := hInvB
    linear_combination this
  rw [hInvBform]
  rw [show core * (1 - X goodVarC * (1 + X goodVarC)⁻¹) =
      core - X goodVarC * (core * (1 + X goodVarC)⁻¹) by ring,
    map_sub, coeff_X_mul_good_zero_c, sub_zero]
  have hnum : goodJacobianNumeratorMv =
      ((1 : GoodMvSeries) - X goodVarB) *
          ((1 : GoodMvSeries) - X goodVarA) +
        X goodVarC *
          (-((1 : GoodMvSeries) - X goodVarB) *
              ((1 : GoodMvSeries) - X goodVarA) -
            X goodVarB * X goodVarA) := by
    simp only [goodJacobianNumeratorMv]
    ring
  dsimp [core]
  rw [hnum]
  rw [show (((1 : GoodMvSeries) - X goodVarB) *
          ((1 : GoodMvSeries) - X goodVarA) +
        X goodVarC *
          (-((1 : GoodMvSeries) - X goodVarB) *
              ((1 : GoodMvSeries) - X goodVarA) -
            X goodVarB * X goodVarA)) *
        (1 + X goodVarB) ^ (2 * y + 1) *
        (1 + X goodVarA) ^ y =
      ((1 : GoodMvSeries) - X goodVarB) *
          ((1 : GoodMvSeries) - X goodVarA) *
          ((1 + X goodVarB) ^ (2 * y + 1) *
            (1 + X goodVarA) ^ y) +
        X goodVarC *
          ((-((1 : GoodMvSeries) - X goodVarB) *
              ((1 : GoodMvSeries) - X goodVarA) -
            X goodVarB * X goodVarA) *
            (1 + X goodVarB) ^ (2 * y + 1) *
            (1 + X goodVarA) ^ y) by ring,
    map_add, coeff_X_mul_good_zero_c, add_zero]
  let separated : GoodMvSeries :=
    (1 + X goodVarB) ^ (2 * y + 1) *
      (1 + X goodVarC) ^ 0 * (1 + X goodVarA) ^ y
  rw [show ((1 : GoodMvSeries) - X goodVarB) *
        ((1 : GoodMvSeries) - X goodVarA) *
        ((1 + X goodVarB) ^ (2 * y + 1) *
          (1 + X goodVarA) ^ y) =
      separated - X goodVarB * separated - X goodVarA * separated +
        X goodVarB * X goodVarA * separated by
          dsimp [separated]
          ring,
    map_add, map_sub]
  simp only [map_sub]
  rw [show coeff ℚ (goodMultiIndex 0 (y + 1) 0) separated =
      (((2 * y + 1).choose (y + 1) : ℕ) : ℚ) by
        convert coeff_separated_good_powers
          y (2 * y + 1) 0 0 (y + 1) 0 using 1
        all_goals simp [separated]
        all_goals ring]
  rw [show coeff ℚ (goodMultiIndex 0 (y + 1) 0)
      (X goodVarB * separated) =
      (((2 * y + 1).choose y : ℕ) : ℚ) by
        convert coeff_Xb_separated_good_powers
          y (2 * y + 1) 0 0 (y + 1) 0 using 1
        all_goals simp [separated, choosePred]
        all_goals ring]
  rw [coeff_X_mul_good_zero]
  have hXaXc : coeff ℚ (goodMultiIndex 0 (y + 1) 0)
      (X goodVarB * X goodVarA * separated) = 0 := by
    apply (MvPowerSeries.X_dvd_iff (s := goodVarA)).mp
      ⟨X goodVarB * separated, by ring⟩
    simp
  rw [hXaXc]
  simp
  rw [Nat.choose_symm_half]
  ring

theorem goodResidueWeight_ray_c_factorization (z : ℕ) :
    goodResidueWeight 0 0 (z + 1) =
      goodJacobianNumeratorMv *
        (1 + X goodVarC) ^ (2 * z + 1) *
        (1 + X goodVarB) ^ z *
        (1 + X goodVarA)⁻¹ := by
  have hInvA := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarC : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarC)
  have hInvC := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarB : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarB)
  rw [goodResidueWeight, goodJacobianDetMv,
    goodJacobianDenominatorMv]
  rw [show goodJacobianNumeratorMv *
      ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
      goodPhiA ^ 0 * goodPhiB ^ 0 * goodPhiC ^ (z + 1) =
      goodJacobianNumeratorMv *
        ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
        (goodPhiA ^ 0 * goodPhiB ^ 0 * goodPhiC ^ (z + 1)) by ring,
    goodPhiPowers_factorization,
    MvPowerSeries.mul_inv_rev, MvPowerSeries.mul_inv_rev]
  simp only [mul_zero, zero_add, pow_zero, mul_one]
  have hPowA : ((1 + X goodVarC : GoodMvSeries) ^ (2 * (z + 1))) =
      (1 + X goodVarC) ^ (2 * z + 1) * (1 + X goodVarC) := by
    rw [show 2 * (z + 1) = (2 * z + 1) + 1 by omega, pow_succ]
  have hPowC : ((1 + X goodVarB : GoodMvSeries) ^ (z + 1)) =
      (1 + X goodVarB) ^ z * (1 + X goodVarB) := by rw [pow_succ]
  rw [show 2 * (z + 1) + 0 = 2 * (z + 1) by omega,
    hPowA, hPowC]
  rw [show goodJacobianNumeratorMv *
        ((1 + X goodVarC)⁻¹ *
          ((1 + X goodVarB)⁻¹ * (1 + X goodVarA)⁻¹)) *
        (1 * ((1 + X goodVarB) ^ z * (1 + X goodVarB)) *
          ((1 + X goodVarC) ^ (2 * z + 1) * (1 + X goodVarC))) =
      goodJacobianNumeratorMv *
        (1 + X goodVarC) ^ (2 * z + 1) *
        (1 + X goodVarB) ^ z *
        (1 + X goodVarA)⁻¹ *
        ((1 + X goodVarC) * (1 + X goodVarC)⁻¹) *
        ((1 + X goodVarB) * (1 + X goodVarB)⁻¹) by ring,
    hInvA, hInvC]
  ring

theorem coeff_goodResidueWeight_ray_c (z : ℕ) :
    coeff ℚ (goodMultiIndex 0 0 (z + 1))
        (goodResidueWeight 0 0 (z + 1)) = 0 := by
  rw [goodResidueWeight_ray_c_factorization]
  let core : GoodMvSeries :=
    goodJacobianNumeratorMv * (1 + X goodVarC) ^ (2 * z + 1) *
      (1 + X goodVarB) ^ z
  change coeff ℚ (goodMultiIndex 0 0 (z + 1))
      (core * (1 + X goodVarA)⁻¹) = 0
  have hInvB := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarA : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarA)
  have hInvBform : ((1 + X goodVarA : GoodMvSeries)⁻¹) =
      1 - X goodVarA * (1 + X goodVarA)⁻¹ := by
    have := hInvB
    linear_combination this
  rw [hInvBform]
  rw [show core * (1 - X goodVarA * (1 + X goodVarA)⁻¹) =
      core - X goodVarA * (core * (1 + X goodVarA)⁻¹) by ring,
    map_sub, coeff_X_mul_good_zero, sub_zero]
  have hnum : goodJacobianNumeratorMv =
      ((1 : GoodMvSeries) - X goodVarC) *
          ((1 : GoodMvSeries) - X goodVarB) +
        X goodVarA *
          (-((1 : GoodMvSeries) - X goodVarC) *
              ((1 : GoodMvSeries) - X goodVarB) -
            X goodVarC * X goodVarB) := by
    simp only [goodJacobianNumeratorMv]
    ring
  dsimp [core]
  rw [hnum]
  rw [show (((1 : GoodMvSeries) - X goodVarC) *
          ((1 : GoodMvSeries) - X goodVarB) +
        X goodVarA *
          (-((1 : GoodMvSeries) - X goodVarC) *
              ((1 : GoodMvSeries) - X goodVarB) -
            X goodVarC * X goodVarB)) *
        (1 + X goodVarC) ^ (2 * z + 1) *
        (1 + X goodVarB) ^ z =
      ((1 : GoodMvSeries) - X goodVarC) *
          ((1 : GoodMvSeries) - X goodVarB) *
          ((1 + X goodVarC) ^ (2 * z + 1) *
            (1 + X goodVarB) ^ z) +
        X goodVarA *
          ((-((1 : GoodMvSeries) - X goodVarC) *
              ((1 : GoodMvSeries) - X goodVarB) -
            X goodVarC * X goodVarB) *
            (1 + X goodVarC) ^ (2 * z + 1) *
            (1 + X goodVarB) ^ z) by ring,
    map_add, coeff_X_mul_good_zero, add_zero]
  let separated : GoodMvSeries :=
    (1 + X goodVarC) ^ (2 * z + 1) *
      (1 + X goodVarA) ^ 0 * (1 + X goodVarB) ^ z
  rw [show ((1 : GoodMvSeries) - X goodVarC) *
        ((1 : GoodMvSeries) - X goodVarB) *
        ((1 + X goodVarC) ^ (2 * z + 1) *
          (1 + X goodVarB) ^ z) =
      separated - X goodVarC * separated - X goodVarB * separated +
        X goodVarC * X goodVarB * separated by
          dsimp [separated]
          ring,
    map_add, map_sub]
  simp only [map_sub]
  rw [show coeff ℚ (goodMultiIndex 0 0 (z + 1)) separated =
      (((2 * z + 1).choose (z + 1) : ℕ) : ℚ) by
        convert coeff_separated_good_powers
          0 z (2 * z + 1) 0 0 (z + 1) using 1
        all_goals simp [separated]
        all_goals ring]
  rw [show coeff ℚ (goodMultiIndex 0 0 (z + 1))
      (X goodVarC * separated) =
      (((2 * z + 1).choose z : ℕ) : ℚ) by
        convert coeff_Xc_separated_good_powers
          0 z (2 * z + 1) 0 0 (z + 1) using 1
        all_goals simp [separated, choosePred]
        all_goals ring]
  rw [coeff_X_mul_good_zero_b]
  have hXaXc : coeff ℚ (goodMultiIndex 0 0 (z + 1))
      (X goodVarC * X goodVarB * separated) = 0 := by
    apply (MvPowerSeries.X_dvd_iff (s := goodVarB)).mp
      ⟨X goodVarC * separated, by ring⟩
    simp
  rw [hXaXc]
  simp
  rw [Nat.choose_symm_half]
  ring

end BenzelProblem6Kernel
