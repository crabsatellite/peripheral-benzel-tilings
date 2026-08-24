import BenzelProblem6Kernel.GoodResiduePolynomialEvaluation
import BenzelProblem6Kernel.GoodGeneratingSeries
import BenzelProblem6Kernel.SpecializedGoodConstantTerm
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Specialized positive and negative Lagrange--Good evaluation
-/

namespace BenzelProblem6Kernel

open MvPowerSeries

noncomputable def goodPositiveNumeratorPolynomial : GoodMvPolynomial :=
  (1 + MvPolynomial.X goodVarA) ^ 2 *
    (1 + MvPolynomial.X goodVarB) ^ 2 *
    (1 + MvPolynomial.X goodVarC) ^ 2

noncomputable def goodOneMinus (coordinate : GoodVariable) :
    GoodMvPolynomial :=
  MvPolynomial.C (1 : ℚ) -
    (MvPolynomial.X coordinate : GoodMvPolynomial)

theorem goodOneMinus_coe (coordinate : GoodVariable) :
    (goodOneMinus coordinate : GoodMvSeries) = 1 - X coordinate := by
  change MvPolynomial.coeToMvPowerSeries.ringHom
      (MvPolynomial.C (1 : ℚ) - MvPolynomial.X coordinate) = _
  rw [map_sub]
  change ((MvPolynomial.C (1 : ℚ) : GoodMvPolynomial) : GoodMvSeries) -
      ((MvPolynomial.X coordinate : GoodMvPolynomial) : GoodMvSeries) = _
  rw [MvPolynomial.coe_C, MvPolynomial.coe_X]
  simp

theorem goodPolynomial_coe_neg (polynomial : GoodMvPolynomial) :
    ((-polynomial : GoodMvPolynomial) : GoodMvSeries) =
      -(polynomial : GoodMvSeries) := by
  change MvPolynomial.coeToMvPowerSeries.ringHom (-polynomial) = _
  rw [map_neg]
  rfl

noncomputable def goodBallotNumeratorPolynomial : GoodMvPolynomial :=
  goodOneMinus goodVarA * goodOneMinus goodVarB *
    goodOneMinus goodVarC

noncomputable def goodJacobianNumeratorPolynomial : GoodMvPolynomial :=
  goodBallotNumeratorPolynomial +
    -((MvPolynomial.X goodVarA : GoodMvPolynomial) *
      MvPolynomial.X goodVarB * MvPolynomial.X goodVarC)

noncomputable def goodJacobianDenominatorPolynomial : GoodMvPolynomial :=
  (1 + MvPolynomial.X goodVarA) *
    (1 + MvPolynomial.X goodVarB) *
    (1 + MvPolynomial.X goodVarC)

theorem goodPositiveNumeratorPolynomial_coe :
    (goodPositiveNumeratorPolynomial : GoodMvSeries) =
      (1 + X goodVarA) ^ 2 * (1 + X goodVarB) ^ 2 *
        (1 + X goodVarC) ^ 2 := by
  simp [goodPositiveNumeratorPolynomial]

theorem goodBallotNumeratorPolynomial_coe :
    (goodBallotNumeratorPolynomial : GoodMvSeries) =
      (1 - X goodVarA) * (1 - X goodVarB) *
        (1 - X goodVarC) := by
  simp [goodBallotNumeratorPolynomial, goodOneMinus_coe]

theorem goodJacobianNumeratorPolynomial_coe :
    (goodJacobianNumeratorPolynomial : GoodMvSeries) =
      goodJacobianNumeratorMv := by
  simp [goodJacobianNumeratorPolynomial, goodJacobianNumeratorMv,
    goodBallotNumeratorPolynomial_coe, goodOneMinus_coe,
    goodPolynomial_coe_neg]
  ring

theorem goodJacobianDenominatorPolynomial_coe :
    (goodJacobianDenominatorPolynomial : GoodMvSeries) =
      goodJacobianDenominatorMv := by
  simp [goodJacobianDenominatorPolynomial, goodJacobianDenominatorMv]

theorem goodPolynomialEval_positiveNumerator :
    goodPolynomialEval goodPositiveNumeratorPolynomial =
      ternarySeries ^ 6 := by
  simp [goodPolynomialEval, goodPositiveNumeratorPolynomial, ternarySeries]
  ring

theorem goodPolynomialEval_ballotNumerator :
    goodPolynomialEval goodBallotNumeratorPolynomial =
      (PowerSeries.C ℚ 2 - ternarySeries) ^ 3 := by
  simp [goodPolynomialEval, goodBallotNumeratorPolynomial,
    goodOneMinus, ternarySeries]
  have h2 : PowerSeries.C ℚ (2 : ℚ) = (2 : PowerSeries ℚ) :=
    map_ofNat (PowerSeries.C ℚ) 2
  rw [h2]
  ring

theorem goodPolynomialEval_jacobianDenominator :
    goodPolynomialEval goodJacobianDenominatorPolynomial =
      ternarySeries ^ 3 := by
  simp [goodPolynomialEval, goodJacobianDenominatorPolynomial,
    ternarySeries]
  ring

theorem goodPolynomialEval_jacobianNumerator :
    goodPolynomialEval goodJacobianNumeratorPolynomial =
      goodLinearDenominator * goodQuadraticDenominator := by
  rw [goodJacobianNumeratorPolynomial,
    map_add, map_neg, map_mul, map_mul,
    goodPolynomialEval_ballotNumerator]
  simp only [goodPolynomialEval_X]
  have h2 : PowerSeries.C ℚ (2 : ℚ) = (2 : PowerSeries ℚ) :=
    map_ofNat (PowerSeries.C ℚ) 2
  have h3 : PowerSeries.C ℚ (3 : ℚ) = (3 : PowerSeries ℚ) :=
    map_ofNat (PowerSeries.C ℚ) 3
  rw [goodLinearDenominator, goodQuadraticDenominator, h2, h3]
  simp [ternarySeries]
  ring

theorem goodJacobianNumeratorMv_constantCoeff :
    constantCoeff GoodVariable ℚ goodJacobianNumeratorMv = 1 := by
  simp [goodJacobianNumeratorMv]

theorem goodJacobianNumeratorMv_ne_zero :
    constantCoeff GoodVariable ℚ goodJacobianNumeratorMv ≠ 0 := by
  rw [goodJacobianNumeratorMv_constantCoeff]
  norm_num

noncomputable def positiveGoodResidueQuotient : GoodMvSeries :=
  ((goodPositiveNumeratorPolynomial *
      goodJacobianDenominatorPolynomial : GoodMvPolynomial) : GoodMvSeries) *
    goodJacobianNumeratorMv⁻¹

noncomputable def negativeGoodResidueQuotient : GoodMvSeries :=
  (goodBallotNumeratorPolynomial : GoodMvSeries) *
    positiveGoodResidueQuotient

theorem positiveGoodResidueQuotient_mul_jacobian :
    positiveGoodResidueQuotient * goodJacobianNumeratorMv =
      ((goodPositiveNumeratorPolynomial *
        goodJacobianDenominatorPolynomial : GoodMvPolynomial) :
          GoodMvSeries) := by
  rw [positiveGoodResidueQuotient]
  rw [show ((goodPositiveNumeratorPolynomial *
          goodJacobianDenominatorPolynomial : GoodMvPolynomial) : GoodMvSeries) *
        goodJacobianNumeratorMv⁻¹ * goodJacobianNumeratorMv =
      ((goodPositiveNumeratorPolynomial *
          goodJacobianDenominatorPolynomial : GoodMvPolynomial) : GoodMvSeries) *
        (goodJacobianNumeratorMv⁻¹ * goodJacobianNumeratorMv) by ring,
    MvPowerSeries.inv_mul_cancel _ goodJacobianNumeratorMv_ne_zero,
    mul_one]

theorem positiveGoodResidueQuotient_mul_weight (x y z : ℕ) :
    positiveGoodResidueQuotient * goodResidueWeight x y z =
      (goodPositiveNumeratorPolynomial : GoodMvSeries) *
        goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z := by
  have hInvH := MvPowerSeries.inv_mul_cancel goodJacobianNumeratorMv
    goodJacobianNumeratorMv_ne_zero
  have hDconst :
      constantCoeff GoodVariable ℚ goodJacobianDenominatorMv = 1 := by
    simp [goodJacobianDenominatorMv]
  have hInvD := MvPowerSeries.mul_inv_cancel goodJacobianDenominatorMv
    (by rw [hDconst]; norm_num)
  rw [positiveGoodResidueQuotient, goodResidueWeight,
    goodJacobianDetMv]
  rw [MvPolynomial.coe_mul,
    goodJacobianDenominatorPolynomial_coe]
  rw [show ((goodPositiveNumeratorPolynomial : GoodMvSeries) *
          goodJacobianDenominatorMv) * goodJacobianNumeratorMv⁻¹ *
        (goodJacobianNumeratorMv * goodJacobianDenominatorMv⁻¹ *
          goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z) =
      (goodPositiveNumeratorPolynomial : GoodMvSeries) *
        goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z *
        (goodJacobianNumeratorMv⁻¹ * goodJacobianNumeratorMv) *
        (goodJacobianDenominatorMv * goodJacobianDenominatorMv⁻¹) by ring,
    hInvH, hInvD]
  ring

theorem positiveGoodNumerator_weight_factorization (x y z : ℕ) :
    (goodPositiveNumeratorPolynomial : GoodMvSeries) *
        goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z =
      (1 + X goodVarA) ^ (2 * x + y + 2) *
        (1 + X goodVarB) ^ (2 * y + z + 2) *
        (1 + X goodVarC) ^ (2 * z + x + 2) := by
  rw [show (goodPositiveNumeratorPolynomial : GoodMvSeries) *
        goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z =
      (goodPositiveNumeratorPolynomial : GoodMvSeries) *
        (goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z) by ring,
    goodPhiPowers_factorization,
    goodPositiveNumeratorPolynomial_coe]
  rw [show 2 * x + y + 2 = 2 + (2 * x + y) by omega,
    show 2 * y + z + 2 = 2 + (2 * y + z) by omega,
    show 2 * z + x + 2 = 2 + (2 * z + x) by omega,
    pow_add, pow_add, pow_add]
  ring

theorem goodResidueTransform_positiveQuotient :
    goodResidueTransform positiveGoodResidueQuotient =
      positiveChiralityGeneratingSeries := by
  apply PowerSeries.ext
  intro degree
  rw [coeff_goodResidueTransform,
    coeff_positiveChiralityGeneratingSeries]
  rw [positiveLevelCount]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [positiveGoodResidueQuotient_mul_weight,
    positiveGoodNumerator_weight_factorization,
    coeff_separated_good_powers,
    positiveChiralityCount]
  norm_cast

theorem positiveChiralityGeneratingSeries_denominator_equation :
    (goodLinearDenominator * goodQuadraticDenominator) *
        positiveChiralityGeneratingSeries = ternarySeries ^ 9 := by
  have hH := goodResidueTransform_polynomial_mul
    goodJacobianNumeratorPolynomial positiveGoodResidueQuotient
  have hFD := goodResidueTransform_polynomial_mul
    (goodPositiveNumeratorPolynomial * goodJacobianDenominatorPolynomial)
    (1 : GoodMvSeries)
  rw [mul_one, goodResidueTransform_one, mul_one] at hFD
  rw [show (goodJacobianNumeratorPolynomial : GoodMvSeries) *
      positiveGoodResidueQuotient =
      positiveGoodResidueQuotient * goodJacobianNumeratorMv by
        rw [goodJacobianNumeratorPolynomial_coe]
        ring,
    positiveGoodResidueQuotient_mul_jacobian,
    hFD,
    goodPolynomialEval_jacobianNumerator,
    goodResidueTransform_positiveQuotient] at hH
  rw [show goodPolynomialEval
      (goodPositiveNumeratorPolynomial * goodJacobianDenominatorPolynomial) =
      ternarySeries ^ 9 by
        rw [map_mul, goodPolynomialEval_positiveNumerator,
          goodPolynomialEval_jacobianDenominator]
        ring] at hH
  exact hH.symm

theorem positiveChiralityGeneratingSeries_eq_good :
    positiveChiralityGeneratingSeries = positiveGoodGeneratingSeries := by
  rw [positiveGoodGeneratingSeries]
  apply (PowerSeries.eq_mul_inv_iff_mul_eq ?_).2
  · rw [← positiveChiralityGeneratingSeries_denominator_equation]
    ring
  · rw [map_mul, goodLinearDenominator_constantCoeff,
      goodQuadraticDenominator_constantCoeff]
    norm_num

theorem negativeGoodResidueQuotient_mul_weight (x y z : ℕ) :
    negativeGoodResidueQuotient * goodResidueWeight x y z =
      (goodBallotNumeratorPolynomial : GoodMvSeries) *
        ((goodPositiveNumeratorPolynomial : GoodMvSeries) *
          goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z) := by
  rw [negativeGoodResidueQuotient]
  rw [show (goodBallotNumeratorPolynomial : GoodMvSeries) *
        positiveGoodResidueQuotient * goodResidueWeight x y z =
      (goodBallotNumeratorPolynomial : GoodMvSeries) *
        (positiveGoodResidueQuotient * goodResidueWeight x y z) by ring,
    positiveGoodResidueQuotient_mul_weight]

theorem goodResidueTransform_negativeQuotient :
    goodResidueTransform negativeGoodResidueQuotient =
      negativeChiralityGeneratingSeries := by
  apply PowerSeries.ext
  intro degree
  rw [coeff_goodResidueTransform,
    coeff_negativeChiralityGeneratingSeries]
  rw [negativeLevelCount]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [negativeGoodResidueQuotient_mul_weight,
    positiveGoodNumerator_weight_factorization,
    goodBallotNumeratorPolynomial_coe]
  let powerA := 2 * point.u + point.v + 2
  let powerB := 2 * point.v + point.w + 2
  let powerC := 2 * point.w + point.u + 2
  let separated : GoodMvSeries :=
    (1 + X goodVarA) ^ powerA *
      (1 + X goodVarB) ^ powerB *
      (1 + X goodVarC) ^ powerC
  change coeff ℚ (goodMultiIndex point.u point.v point.w)
      ((1 - X goodVarA) * (1 - X goodVarB) *
        (1 - X goodVarC) * separated) = _
  rw [show (1 - X goodVarA) * (1 - X goodVarB) *
        (1 - X goodVarC) * separated =
      separated - X goodVarA * separated - X goodVarB * separated -
          X goodVarC * separated +
        X goodVarA * X goodVarB * separated +
        X goodVarA * X goodVarC * separated +
        X goodVarB * X goodVarC * separated -
        X goodVarA * X goodVarB * X goodVarC * separated by ring]
  simp only [map_sub, map_add]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w) separated =
      ((powerA.choose point.u : ℚ) * powerB.choose point.v *
        powerC.choose point.w) by
        exact coeff_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w)
      (X goodVarA * separated) =
      ((choosePred powerA point.u : ℕ) : ℚ) * powerB.choose point.v *
        powerC.choose point.w by
        exact coeff_Xa_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w)
      (X goodVarB * separated) =
      ((powerA.choose point.u : ℚ) * choosePred powerB point.v *
        powerC.choose point.w) by
        exact coeff_Xb_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w)
      (X goodVarC * separated) =
      ((powerA.choose point.u : ℚ) * powerB.choose point.v *
        choosePred powerC point.w) by
        exact coeff_Xc_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w)
      (X goodVarA * X goodVarB * separated) =
      ((choosePred powerA point.u : ℕ) : ℚ) *
        choosePred powerB point.v * powerC.choose point.w by
        exact coeff_XaXb_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w)
      (X goodVarA * X goodVarC * separated) =
      ((choosePred powerA point.u : ℕ) : ℚ) * powerB.choose point.v *
        choosePred powerC point.w by
        exact coeff_XaXc_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w)
      (X goodVarB * X goodVarC * separated) =
      ((powerA.choose point.u : ℚ) * choosePred powerB point.v *
        choosePred powerC point.w) by
        exact coeff_XbXc_separated_good_powers _ _ _ _ _ _]
  rw [show coeff ℚ (goodMultiIndex point.u point.v point.w)
      (X goodVarA * X goodVarB * X goodVarC * separated) =
      ((choosePred powerA point.u : ℕ) : ℚ) *
        choosePred powerB point.v * choosePred powerC point.w by
        exact coeff_XaXbXc_separated_good_powers _ _ _ _ _ _]
  rw [negativeChiralityCount]
  simp only [← ballotLaurentCoefficient_eq_ballotNumber,
    ballotLaurentCoefficient]
  have hleA : choosePred powerA point.u ≤ powerA.choose point.u := by
    dsimp [powerA]
    exact choosePred_le_chirality point.u point.v
  have hleB : choosePred powerB point.v ≤ powerB.choose point.v := by
    dsimp [powerB]
    exact choosePred_le_chirality point.v point.w
  have hleC : choosePred powerC point.w ≤ powerC.choose point.w := by
    dsimp [powerC]
    exact choosePred_le_chirality point.w point.u
  dsimp [powerA, powerB, powerC]
  rw [Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub hleA, Nat.cast_sub hleB, Nat.cast_sub hleC]
  ring

theorem negativeChiralityGeneratingSeries_eq_good :
    negativeChiralityGeneratingSeries = negativeGoodGeneratingSeries := by
  have hpoly := goodResidueTransform_polynomial_mul
    goodBallotNumeratorPolynomial positiveGoodResidueQuotient
  rw [show (goodBallotNumeratorPolynomial : GoodMvSeries) *
      positiveGoodResidueQuotient = negativeGoodResidueQuotient by rfl,
    goodResidueTransform_negativeQuotient,
    goodPolynomialEval_ballotNumerator,
    goodResidueTransform_positiveQuotient,
    positiveChiralityGeneratingSeries_eq_good] at hpoly
  rw [negativeGoodGeneratingSeries]
  exact hpoly

end BenzelProblem6Kernel
