import BenzelProblem6Kernel.GoodResidueKernel

/-!
# Coordinate transfer for the specialized Good residue transform

Multiplication by a coordinate shifts the extracted multi-index.  Reindexing
the positive face of the simplex gives Good's fundamental transfer relation
`M(x_i g) = t M(phi_i g)`.
-/

namespace BenzelProblem6Kernel

open MvPowerSeries
open scoped BigOperators

theorem goodResidueTransform_mul_a (series : GoodMvSeries) :
    goodResidueTransform (X goodVarA * series) =
      PowerSeries.X * goodResidueTransform (goodPhiA * series) := by
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero =>
      rw [coeff_goodResidueTransform,
        PowerSeries.coeff_zero_X_mul]
      apply Finset.sum_eq_zero
      intro point _
      have hu : point.u = 0 := by
        have := point.sum_eq
        omega
      rw [show (X goodVarA * series) *
          goodResidueWeight point.u point.v point.w =
          X goodVarA *
            (series * goodResidueWeight point.u point.v point.w) by ring,
        hu, coeff_X_mul_good_zero]
  | succ degree =>
      rw [coeff_goodResidueTransform]
      have hshift :
          PowerSeries.coeff ℚ (degree + 1)
              (PowerSeries.X *
                goodResidueTransform (goodPhiA * series)) =
            PowerSeries.coeff ℚ degree
              (goodResidueTransform (goodPhiA * series)) := by
        rw [show (PowerSeries.X : PowerSeries ℚ) = PowerSeries.X ^ 1 by simp]
        rw [PowerSeries.coeff_X_pow_mul]
      rw [hshift, coeff_goodResidueTransform]
      have hpositive :
          (∑ point : SimplexPoint (degree + 1),
              coeff ℚ (goodMultiIndex point.u point.v point.w)
                ((X goodVarA * series) *
                  goodResidueWeight point.u point.v point.w)) =
            ∑ point : PositiveUPoint (degree + 1),
              coeff ℚ
                (goodMultiIndex point.1.u point.1.v point.1.w)
                ((X goodVarA * series) *
                  goodResidueWeight point.1.u point.1.v point.1.w) := by
        apply sum_eq_subtype_of_zero
        intro point hnot
        have hu : point.u = 0 := by omega
        rw [show (X goodVarA * series) *
            goodResidueWeight point.u point.v point.w =
            X goodVarA *
              (series * goodResidueWeight point.u point.v point.w) by ring,
          hu, coeff_X_mul_good_zero]
      rw [hpositive]
      symm
      apply Fintype.sum_equiv (liftUEquiv degree)
      intro point
      rcases liftUEquiv_coordinates degree point with ⟨hu, hv, hw⟩
      rw [hu, hv, hw]
      rw [show (X goodVarA * series) *
          goodResidueWeight (point.u + 1) point.v point.w =
          X goodVarA *
            (series * goodResidueWeight (point.u + 1) point.v point.w) by ring,
        coeff_X_mul_good_succ,
        goodResidueWeight_succ_a]
      congr 1
      ring

theorem goodResidueTransform_mul_b (series : GoodMvSeries) :
    goodResidueTransform (X goodVarB * series) =
      PowerSeries.X * goodResidueTransform (goodPhiB * series) := by
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero =>
      rw [coeff_goodResidueTransform,
        PowerSeries.coeff_zero_X_mul]
      apply Finset.sum_eq_zero
      intro point _
      have hv : point.v = 0 := by
        have := point.sum_eq
        omega
      rw [show (X goodVarB * series) *
          goodResidueWeight point.u point.v point.w =
          X goodVarB *
            (series * goodResidueWeight point.u point.v point.w) by ring,
        hv, coeff_X_mul_good_zero_b]
  | succ degree =>
      rw [coeff_goodResidueTransform]
      have hshift :
          PowerSeries.coeff ℚ (degree + 1)
              (PowerSeries.X *
                goodResidueTransform (goodPhiB * series)) =
            PowerSeries.coeff ℚ degree
              (goodResidueTransform (goodPhiB * series)) := by
        rw [show (PowerSeries.X : PowerSeries ℚ) = PowerSeries.X ^ 1 by simp]
        rw [PowerSeries.coeff_X_pow_mul]
      rw [hshift, coeff_goodResidueTransform]
      have hpositive :
          (∑ point : SimplexPoint (degree + 1),
              coeff ℚ (goodMultiIndex point.u point.v point.w)
                ((X goodVarB * series) *
                  goodResidueWeight point.u point.v point.w)) =
            ∑ point : PositiveVPoint (degree + 1),
              coeff ℚ
                (goodMultiIndex point.1.u point.1.v point.1.w)
                ((X goodVarB * series) *
                  goodResidueWeight point.1.u point.1.v point.1.w) := by
        apply sum_eq_subtype_of_zero
        intro point hnot
        have hv : point.v = 0 := by omega
        rw [show (X goodVarB * series) *
            goodResidueWeight point.u point.v point.w =
            X goodVarB *
              (series * goodResidueWeight point.u point.v point.w) by ring,
          hv, coeff_X_mul_good_zero_b]
      rw [hpositive]
      symm
      apply Fintype.sum_equiv (liftVEquiv degree)
      intro point
      rcases liftVEquiv_coordinates degree point with ⟨hu, hv, hw⟩
      rw [hu, hv, hw]
      rw [show (X goodVarB * series) *
          goodResidueWeight point.u (point.v + 1) point.w =
          X goodVarB *
            (series * goodResidueWeight point.u (point.v + 1) point.w) by ring,
        coeff_X_mul_good_succ_b,
        goodResidueWeight_succ_b]
      congr 1
      ring

theorem goodResidueTransform_mul_c (series : GoodMvSeries) :
    goodResidueTransform (X goodVarC * series) =
      PowerSeries.X * goodResidueTransform (goodPhiC * series) := by
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero =>
      rw [coeff_goodResidueTransform,
        PowerSeries.coeff_zero_X_mul]
      apply Finset.sum_eq_zero
      intro point _
      have hw : point.w = 0 := by
        have := point.sum_eq
        omega
      rw [show (X goodVarC * series) *
          goodResidueWeight point.u point.v point.w =
          X goodVarC *
            (series * goodResidueWeight point.u point.v point.w) by ring,
        hw, coeff_X_mul_good_zero_c]
  | succ degree =>
      rw [coeff_goodResidueTransform]
      have hshift :
          PowerSeries.coeff ℚ (degree + 1)
              (PowerSeries.X *
                goodResidueTransform (goodPhiC * series)) =
            PowerSeries.coeff ℚ degree
              (goodResidueTransform (goodPhiC * series)) := by
        rw [show (PowerSeries.X : PowerSeries ℚ) = PowerSeries.X ^ 1 by simp]
        rw [PowerSeries.coeff_X_pow_mul]
      rw [hshift, coeff_goodResidueTransform]
      have hpositive :
          (∑ point : SimplexPoint (degree + 1),
              coeff ℚ (goodMultiIndex point.u point.v point.w)
                ((X goodVarC * series) *
                  goodResidueWeight point.u point.v point.w)) =
            ∑ point : PositiveWPoint (degree + 1),
              coeff ℚ
                (goodMultiIndex point.1.u point.1.v point.1.w)
                ((X goodVarC * series) *
                  goodResidueWeight point.1.u point.1.v point.1.w) := by
        apply sum_eq_subtype_of_zero
        intro point hnot
        have hw : point.w = 0 := by omega
        rw [show (X goodVarC * series) *
            goodResidueWeight point.u point.v point.w =
            X goodVarC *
              (series * goodResidueWeight point.u point.v point.w) by ring,
          hw, coeff_X_mul_good_zero_c]
      rw [hpositive]
      symm
      apply Fintype.sum_equiv (liftWEquiv degree)
      intro point
      rcases liftWEquiv_coordinates degree point with ⟨hu, hv, hw⟩
      rw [hu, hv, hw]
      rw [show (X goodVarC * series) *
          goodResidueWeight point.u point.v (point.w + 1) =
          X goodVarC *
            (series * goodResidueWeight point.u point.v (point.w + 1)) by ring,
        coeff_X_mul_good_succ_c,
        goodResidueWeight_succ_c]
      congr 1
      ring

end BenzelProblem6Kernel
