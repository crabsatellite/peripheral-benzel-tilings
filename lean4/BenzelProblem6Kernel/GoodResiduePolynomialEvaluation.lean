import BenzelProblem6Kernel.GoodResidueDelta
import BenzelProblem6Kernel.GoodResidueTransfer
import Mathlib.Algebra.MvPolynomial.Eval
import BenzelProblem6Kernel.TernarySeriesEquation

/-!
# Polynomial evaluation under the specialized Good transform
-/

namespace BenzelProblem6Kernel

open MvPowerSeries
open scoped BigOperators

abbrev GoodMvPolynomial := MvPolynomial GoodVariable ℚ

noncomputable def goodPhiAPolynomial : GoodMvPolynomial :=
  (1 + MvPolynomial.X goodVarA) ^ 2 *
    (1 + MvPolynomial.X goodVarC)

noncomputable def goodPhiBPolynomial : GoodMvPolynomial :=
  (1 + MvPolynomial.X goodVarB) ^ 2 *
    (1 + MvPolynomial.X goodVarA)

noncomputable def goodPhiCPolynomial : GoodMvPolynomial :=
  (1 + MvPolynomial.X goodVarC) ^ 2 *
    (1 + MvPolynomial.X goodVarB)

noncomputable def goodPolynomialEval : GoodMvPolynomial →+* PowerSeries ℚ :=
  MvPolynomial.eval₂Hom (PowerSeries.C ℚ)
    (fun _coordinate => ternarySmallRoot)

theorem goodPhiAPolynomial_coe :
    (goodPhiAPolynomial : GoodMvSeries) = goodPhiA := by
  simp [goodPhiAPolynomial, goodPhiA]

theorem goodPhiBPolynomial_coe :
    (goodPhiBPolynomial : GoodMvSeries) = goodPhiB := by
  simp [goodPhiBPolynomial, goodPhiB]

theorem goodPhiCPolynomial_coe :
    (goodPhiCPolynomial : GoodMvSeries) = goodPhiC := by
  simp [goodPhiCPolynomial, goodPhiC]

theorem goodPolynomialEval_X (coordinate : GoodVariable) :
    goodPolynomialEval (MvPolynomial.X coordinate) = ternarySmallRoot := by
  simp [goodPolynomialEval]

theorem goodPolynomialEval_phiA :
    goodPolynomialEval goodPhiAPolynomial = ternarySeries ^ 3 := by
  simp [goodPolynomialEval, goodPhiAPolynomial, ternarySeries]
  ring

theorem goodPolynomialEval_phiB :
    goodPolynomialEval goodPhiBPolynomial = ternarySeries ^ 3 := by
  simp [goodPolynomialEval, goodPhiBPolynomial, ternarySeries]
  ring

theorem goodPolynomialEval_phiC :
    goodPolynomialEval goodPhiCPolynomial = ternarySeries ^ 3 := by
  simp [goodPolynomialEval, goodPhiCPolynomial, ternarySeries]
  ring

theorem goodResidueTransform_add (left right : GoodMvSeries) :
    goodResidueTransform (left + right) =
      goodResidueTransform left + goodResidueTransform right := by
  apply PowerSeries.ext
  intro degree
  simp only [coeff_goodResidueTransform, map_add,
    add_mul, Finset.sum_add_distrib]

theorem goodResidueTransform_C_mul (scalar : ℚ) (series : GoodMvSeries) :
    goodResidueTransform (C GoodVariable ℚ scalar * series) =
      PowerSeries.C ℚ scalar * goodResidueTransform series := by
  apply PowerSeries.ext
  intro degree
  rw [coeff_goodResidueTransform, PowerSeries.coeff_C_mul,
    coeff_goodResidueTransform]
  calc
    (∑ point : SimplexPoint degree,
        coeff ℚ (goodMultiIndex point.u point.v point.w)
          ((C GoodVariable ℚ scalar * series) *
            goodResidueWeight point.u point.v point.w)) =
      ∑ point : SimplexPoint degree,
        scalar * coeff ℚ (goodMultiIndex point.u point.v point.w)
          (series * goodResidueWeight point.u point.v point.w) := by
        apply Finset.sum_congr rfl
        intro point _
        rw [show (C GoodVariable ℚ scalar * series) *
            goodResidueWeight point.u point.v point.w =
            C GoodVariable ℚ scalar *
              (series * goodResidueWeight point.u point.v point.w) by ring,
          MvPowerSeries.coeff_C_mul]
    _ = _ := by rw [Finset.mul_sum]

theorem ternarySmallRoot_eq_X_mul :
    ternarySmallRoot = PowerSeries.X * ternarySeries ^ 3 := by
  simpa [ternaryStep, ternarySeries] using ternarySmallRoot_equation

theorem goodResidueTransform_polynomial_mul_coeff :
    ∀ degree : ℕ, ∀ (polynomial : GoodMvPolynomial) (series : GoodMvSeries),
      PowerSeries.coeff ℚ degree
          (goodResidueTransform ((polynomial : GoodMvSeries) * series)) =
        PowerSeries.coeff ℚ degree
          (goodPolynomialEval polynomial * goodResidueTransform series) := by
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree ih =>
      intro polynomial
      induction polynomial using MvPolynomial.induction_on with
      | h_C scalar =>
          intro series
          simp only [map_mul, MvPolynomial.coe_C,
            MvPolynomial.eval₂Hom_C, goodPolynomialEval]
          rw [goodResidueTransform_C_mul]
      | h_add left right hleft hright =>
          intro series
          rw [show ((left + right : GoodMvPolynomial) : GoodMvSeries) * series =
              (left : GoodMvSeries) * series +
                (right : GoodMvSeries) * series by push_cast; ring,
            goodResidueTransform_add]
          rw [show goodPolynomialEval (left + right) =
              goodPolynomialEval left + goodPolynomialEval right by simp]
          rw [add_mul, map_add, hleft, hright, map_add]
      | h_X polynomial coordinate hpolynomial =>
          intro series
          have hcoe :
              ((polynomial * MvPolynomial.X coordinate : GoodMvPolynomial) :
                  GoodMvSeries) * series =
                X coordinate * ((polynomial : GoodMvSeries) * series) := by
            push_cast
            ring
          rw [hcoe]
          rw [show goodPolynomialEval
              (polynomial * MvPolynomial.X coordinate) =
              goodPolynomialEval polynomial * ternarySmallRoot by
                rw [map_mul, goodPolynomialEval_X]]
          cases coordinate using Fin.cases with
          | zero =>
              rw [show (0 : GoodVariable) = goodVarA by rfl]
              rw [goodResidueTransform_mul_a]
              cases degree with
              | zero =>
                  rw [PowerSeries.coeff_zero_X_mul,
                    ternarySmallRoot_eq_X_mul]
                  rw [show goodPolynomialEval polynomial *
                      (PowerSeries.X * ternarySeries ^ 3) *
                      goodResidueTransform series =
                    PowerSeries.X * (goodPolynomialEval polynomial *
                      ternarySeries ^ 3 * goodResidueTransform series) by ring,
                    PowerSeries.coeff_zero_X_mul]
              | succ degree =>
                  rw [show (PowerSeries.X : PowerSeries ℚ) =
                      PowerSeries.X ^ 1 by simp,
                    PowerSeries.coeff_X_pow_mul]
                  rw [show goodPhiA * ((polynomial : GoodMvSeries) * series) =
                      ((goodPhiAPolynomial * polynomial : GoodMvPolynomial) :
                        GoodMvSeries) * series by
                        rw [← goodPhiAPolynomial_coe]
                        push_cast
                        ring,
                    ih degree (by omega)]
                  rw [show goodPolynomialEval
                      (goodPhiAPolynomial * polynomial) =
                      ternarySeries ^ 3 * goodPolynomialEval polynomial by
                        rw [map_mul, goodPolynomialEval_phiA],
                    ternarySmallRoot_eq_X_mul]
                  rw [show goodPolynomialEval polynomial *
                      (PowerSeries.X * ternarySeries ^ 3) *
                      goodResidueTransform series =
                      PowerSeries.X *
                        (goodPolynomialEval goodPhiAPolynomial *
                          goodPolynomialEval polynomial *
                          goodResidueTransform series) by
                            rw [goodPolynomialEval_phiA]
                            ring]
                  rw [show (PowerSeries.X : PowerSeries ℚ) =
                      PowerSeries.X ^ 1 by simp,
                    PowerSeries.coeff_X_pow_mul,
                    goodPolynomialEval_phiA]
          | succ coordinate =>
              cases coordinate using Fin.cases with
              | zero =>
                  rw [show (Fin.succ 0 : GoodVariable) = goodVarB by rfl]
                  rw [goodResidueTransform_mul_b]
                  cases degree with
                  | zero =>
                      rw [PowerSeries.coeff_zero_X_mul,
                        ternarySmallRoot_eq_X_mul]
                      rw [show goodPolynomialEval polynomial *
                          (PowerSeries.X * ternarySeries ^ 3) *
                          goodResidueTransform series =
                        PowerSeries.X * (goodPolynomialEval polynomial *
                          ternarySeries ^ 3 * goodResidueTransform series) by ring,
                        PowerSeries.coeff_zero_X_mul]
                  | succ degree =>
                      rw [show (PowerSeries.X : PowerSeries ℚ) =
                          PowerSeries.X ^ 1 by simp,
                        PowerSeries.coeff_X_pow_mul]
                      rw [show goodPhiB * ((polynomial : GoodMvSeries) * series) =
                          ((goodPhiBPolynomial * polynomial : GoodMvPolynomial) :
                            GoodMvSeries) * series by
                            rw [← goodPhiBPolynomial_coe]
                            push_cast
                            ring,
                        ih degree (by omega)]
                      rw [show goodPolynomialEval
                          (goodPhiBPolynomial * polynomial) =
                          ternarySeries ^ 3 * goodPolynomialEval polynomial by
                            rw [map_mul, goodPolynomialEval_phiB],
                        ternarySmallRoot_eq_X_mul]
                      rw [show goodPolynomialEval polynomial *
                          (PowerSeries.X * ternarySeries ^ 3) *
                          goodResidueTransform series =
                          PowerSeries.X *
                            (goodPolynomialEval goodPhiBPolynomial *
                              goodPolynomialEval polynomial *
                              goodResidueTransform series) by
                                rw [goodPolynomialEval_phiB]
                                ring]
                      rw [show (PowerSeries.X : PowerSeries ℚ) =
                          PowerSeries.X ^ 1 by simp,
                        PowerSeries.coeff_X_pow_mul,
                        goodPolynomialEval_phiB]
              | succ coordinate =>
                  have hcoord : coordinate = 0 := Fin.eq_zero coordinate
                  subst coordinate
                  rw [show (Fin.succ (Fin.succ 0) : GoodVariable) =
                    goodVarC by rfl]
                  rw [goodResidueTransform_mul_c]
                  cases degree with
                  | zero =>
                      rw [PowerSeries.coeff_zero_X_mul,
                        ternarySmallRoot_eq_X_mul]
                      rw [show goodPolynomialEval polynomial *
                          (PowerSeries.X * ternarySeries ^ 3) *
                          goodResidueTransform series =
                        PowerSeries.X * (goodPolynomialEval polynomial *
                          ternarySeries ^ 3 * goodResidueTransform series) by ring,
                        PowerSeries.coeff_zero_X_mul]
                  | succ degree =>
                      rw [show (PowerSeries.X : PowerSeries ℚ) =
                          PowerSeries.X ^ 1 by simp,
                        PowerSeries.coeff_X_pow_mul]
                      rw [show goodPhiC * ((polynomial : GoodMvSeries) * series) =
                          ((goodPhiCPolynomial * polynomial : GoodMvPolynomial) :
                            GoodMvSeries) * series by
                            rw [← goodPhiCPolynomial_coe]
                            push_cast
                            ring,
                        ih degree (by omega)]
                      rw [show goodPolynomialEval
                          (goodPhiCPolynomial * polynomial) =
                          ternarySeries ^ 3 * goodPolynomialEval polynomial by
                            rw [map_mul, goodPolynomialEval_phiC],
                        ternarySmallRoot_eq_X_mul]
                      rw [show goodPolynomialEval polynomial *
                          (PowerSeries.X * ternarySeries ^ 3) *
                          goodResidueTransform series =
                          PowerSeries.X *
                            (goodPolynomialEval goodPhiCPolynomial *
                              goodPolynomialEval polynomial *
                              goodResidueTransform series) by
                                rw [goodPolynomialEval_phiC]
                                ring]
                      rw [show (PowerSeries.X : PowerSeries ℚ) =
                          PowerSeries.X ^ 1 by simp,
                        PowerSeries.coeff_X_pow_mul,
                        goodPolynomialEval_phiC]

theorem goodResidueTransform_polynomial_mul
    (polynomial : GoodMvPolynomial) (series : GoodMvSeries) :
    goodResidueTransform ((polynomial : GoodMvSeries) * series) =
      goodPolynomialEval polynomial * goodResidueTransform series := by
  apply PowerSeries.ext
  exact fun degree =>
    goodResidueTransform_polynomial_mul_coeff degree polynomial series

end BenzelProblem6Kernel
