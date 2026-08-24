import BenzelProblem6Kernel.GoodSeparatedCoefficient

/-!
# Positive-index form of the Good residue weight
-/

namespace BenzelProblem6Kernel

open MvPowerSeries

theorem goodPhiPowers_factorization (x y z : ℕ) :
    goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z =
      (1 + X goodVarA) ^ (2 * x + y) *
        (1 + X goodVarB) ^ (2 * y + z) *
        (1 + X goodVarC) ^ (2 * z + x) := by
  let A : GoodMvSeries := 1 + X goodVarA
  let B : GoodMvSeries := 1 + X goodVarB
  let Cc : GoodMvSeries := 1 + X goodVarC
  change (A ^ 2 * Cc) ^ x * (B ^ 2 * A) ^ y *
      (Cc ^ 2 * B) ^ z =
    A ^ (2 * x + y) * B ^ (2 * y + z) * Cc ^ (2 * z + x)
  rw [mul_pow, mul_pow, mul_pow]
  rw [show (A ^ 2) ^ x = A ^ (2 * x) by rw [pow_mul],
    show (B ^ 2) ^ y = B ^ (2 * y) by rw [pow_mul],
    show (Cc ^ 2) ^ z = Cc ^ (2 * z) by rw [pow_mul]]
  calc
    A ^ (2 * x) * Cc ^ x * (B ^ (2 * y) * A ^ y) *
        (Cc ^ (2 * z) * B ^ z) =
      (A ^ (2 * x) * A ^ y) * (B ^ (2 * y) * B ^ z) *
        (Cc ^ (2 * z) * Cc ^ x) := by ring
    _ = _ := by rw [← pow_add, ← pow_add, ← pow_add]

theorem goodAxis_constantCoeff_ne_zero (coordinate : GoodVariable) :
    constantCoeff GoodVariable ℚ (1 + X coordinate : GoodMvSeries) ≠ 0 := by
  simp

theorem goodResidueWeight_factorization_of_axis_positive
    (x y z : ℕ)
    (hApos : 0 < 2 * x + y) (hBpos : 0 < 2 * y + z)
    (hCpos : 0 < 2 * z + x) :
    goodResidueWeight x y z =
      goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * x + y - 1) *
        (1 + X goodVarB) ^ (2 * y + z - 1) *
        (1 + X goodVarC) ^ (2 * z + x - 1) := by
  have hA : 2 * x + y = (2 * x + y - 1) + 1 := by omega
  have hB : 2 * y + z = (2 * y + z - 1) + 1 := by omega
  have hC : 2 * z + x = (2 * z + x - 1) + 1 := by omega
  have hInvA := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarA : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarA)
  have hInvB := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarB : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarB)
  have hInvC := MvPowerSeries.mul_inv_cancel
    (1 + X goodVarC : GoodMvSeries)
    (goodAxis_constantCoeff_ne_zero goodVarC)
  rw [goodResidueWeight, goodJacobianDetMv,
    goodJacobianDenominatorMv]
  rw [show goodJacobianNumeratorMv *
      ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
      goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z =
      goodJacobianNumeratorMv *
        ((1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC))⁻¹ *
        (goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z) by ring,
    goodPhiPowers_factorization,
    MvPowerSeries.mul_inv_rev, MvPowerSeries.mul_inv_rev,
    hA, hB, hC, pow_succ, pow_succ, pow_succ]
  rw [show goodJacobianNumeratorMv *
        ((1 + X goodVarC)⁻¹ *
          ((1 + X goodVarB)⁻¹ * (1 + X goodVarA)⁻¹)) *
        (((1 + X goodVarA) ^ (2 * x + y - 1) *
            (1 + X goodVarA)) *
          ((1 + X goodVarB) ^ (2 * y + z - 1) *
            (1 + X goodVarB)) *
          ((1 + X goodVarC) ^ (2 * z + x - 1) *
            (1 + X goodVarC))) =
      goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * x + y - 1) *
        (1 + X goodVarB) ^ (2 * y + z - 1) *
        (1 + X goodVarC) ^ (2 * z + x - 1) *
        ((1 + X goodVarA) * (1 + X goodVarA)⁻¹) *
        ((1 + X goodVarB) * (1 + X goodVarB)⁻¹) *
        ((1 + X goodVarC) * (1 + X goodVarC)⁻¹) by ring,
    hInvA, hInvB, hInvC]
  have hAm : 2 * x + y - 1 + 1 - 1 = 2 * x + y - 1 := by omega
  have hBm : 2 * y + z - 1 + 1 - 1 = 2 * y + z - 1 := by omega
  have hCm : 2 * z + x - 1 + 1 - 1 = 2 * z + x - 1 := by omega
  rw [hAm, hBm, hCm]
  ring

theorem goodResidueWeight_positive_factorization
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    goodResidueWeight x y z =
      goodJacobianNumeratorMv *
        (1 + X goodVarA) ^ (2 * x + y - 1) *
        (1 + X goodVarB) ^ (2 * y + z - 1) *
        (1 + X goodVarC) ^ (2 * z + x - 1) :=
  goodResidueWeight_factorization_of_axis_positive x y z
    (by omega) (by omega) (by omega)

end BenzelProblem6Kernel
