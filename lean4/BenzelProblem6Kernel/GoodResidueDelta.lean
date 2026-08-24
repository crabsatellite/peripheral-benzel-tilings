import BenzelProblem6Kernel.GoodResidueWeightRay

/-!
# Delta identity for the specialized Good residue weight
-/

namespace BenzelProblem6Kernel

open MvPowerSeries

theorem coeff_goodResidueWeight_origin :
    coeff ℚ (goodMultiIndex 0 0 0) (goodResidueWeight 0 0 0) = 1 := by
  have hden : constantCoeff GoodVariable ℚ goodJacobianDenominatorMv = 1 := by
    simp [goodJacobianDenominatorMv]
  simp only [goodResidueWeight, pow_zero, mul_one, goodJacobianDetMv,
    goodMultiIndex]
  rw [show Finsupp.single goodVarA 0 + Finsupp.single goodVarB 0 +
      Finsupp.single goodVarC 0 = 0 by simp,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    MvPowerSeries.constantCoeff_inv, hden, inv_one, mul_one]
  simp [goodJacobianNumeratorMv]

theorem coeff_goodResidueWeight_delta (x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z) (goodResidueWeight x y z) =
      goodDeterminantCoefficient x y z := by
  rcases x with _ | x
  · rcases y with _ | y
    · rcases z with _ | z
      · rw [coeff_goodResidueWeight_origin,
          goodDeterminantCoefficient_origin]
      · rw [coeff_goodResidueWeight_ray_c,
          goodDeterminantCoefficient_zero_of_positive]
        omega
    · rcases z with _ | z
      · rw [coeff_goodResidueWeight_ray_b,
          goodDeterminantCoefficient_zero_of_positive]
        omega
      · exact coeff_goodResidueWeight_of_axis_positive
          0 (y + 1) (z + 1) (by omega) (by omega) (by omega)
  · rcases y with _ | y
    · rcases z with _ | z
      · rw [coeff_goodResidueWeight_ray_a,
          goodDeterminantCoefficient_zero_of_positive]
        omega
      · exact coeff_goodResidueWeight_of_axis_positive
          (x + 1) 0 (z + 1) (by omega) (by omega) (by omega)
    · rcases z with _ | z
      · exact coeff_goodResidueWeight_of_axis_positive
          (x + 1) (y + 1) 0 (by omega) (by omega) (by omega)
      · exact coeff_goodResidueWeight_of_axis_positive
          (x + 1) (y + 1) (z + 1) (by omega) (by omega) (by omega)

theorem goodResidueTransform_one :
    goodResidueTransform 1 = 1 := by
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero =>
      rw [coeff_goodResidueTransform]
      have hpoint (point : SimplexPoint 0) :
          point.u = 0 ∧ point.v = 0 ∧ point.w = 0 := by
        have := point.sum_eq
        omega
      simp_rw [show ∀ point : SimplexPoint 0,
          coeff ℚ (goodMultiIndex point.u point.v point.w)
              (1 * goodResidueWeight point.u point.v point.w) = 1 by
        intro point
        rcases hpoint point with ⟨hu, hv, hw⟩
        rw [hu, hv, hw, one_mul, coeff_goodResidueWeight_origin]]
      simp [card_simplexPoint]
  | succ degree =>
      rw [coeff_goodResidueTransform]
      rw [PowerSeries.coeff_one, if_neg (by omega)]
      apply Finset.sum_eq_zero
      intro point _
      rw [one_mul, coeff_goodResidueWeight_delta,
        goodDeterminantCoefficient_zero_of_positive]
      have := point.sum_eq
      omega

end BenzelProblem6Kernel
