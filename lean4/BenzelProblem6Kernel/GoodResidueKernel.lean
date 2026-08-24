import BenzelProblem6Kernel.GoodDeterminantCoefficient
import BenzelProblem6Kernel.WZSimplexEquiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal residue kernel for the specialized Good transform
-/

namespace BenzelProblem6Kernel

open MvPowerSeries
open scoped BigOperators

abbrev GoodVariable := Fin 3
abbrev GoodMvSeries := MvPowerSeries GoodVariable ℚ

def goodVarA : GoodVariable := 0
def goodVarB : GoodVariable := 1
def goodVarC : GoodVariable := 2

noncomputable def goodPhiA : GoodMvSeries :=
  (1 + X goodVarA) ^ 2 * (1 + X goodVarC)

noncomputable def goodPhiB : GoodMvSeries :=
  (1 + X goodVarB) ^ 2 * (1 + X goodVarA)

noncomputable def goodPhiC : GoodMvSeries :=
  (1 + X goodVarC) ^ 2 * (1 + X goodVarB)

noncomputable def goodJacobianNumeratorMv : GoodMvSeries :=
  (1 - X goodVarA) * (1 - X goodVarB) * (1 - X goodVarC) -
    X goodVarA * X goodVarB * X goodVarC

noncomputable def goodJacobianDenominatorMv : GoodMvSeries :=
  (1 + X goodVarA) * (1 + X goodVarB) * (1 + X goodVarC)

noncomputable def goodJacobianDetMv : GoodMvSeries :=
  goodJacobianNumeratorMv * goodJacobianDenominatorMv⁻¹

noncomputable def goodMultiIndex (x y z : ℕ) : GoodVariable →₀ ℕ :=
  Finsupp.single goodVarA x + Finsupp.single goodVarB y +
    Finsupp.single goodVarC z

@[simp] theorem goodMultiIndex_a (x y z : ℕ) :
    goodMultiIndex x y z goodVarA = x := by
  simp [goodMultiIndex, goodVarA, goodVarB, goodVarC]

@[simp] theorem goodMultiIndex_b (x y z : ℕ) :
    goodMultiIndex x y z goodVarB = y := by
  simp [goodMultiIndex, goodVarA, goodVarB, goodVarC]

@[simp] theorem goodMultiIndex_c (x y z : ℕ) :
    goodMultiIndex x y z goodVarC = z := by
  simp [goodMultiIndex, goodVarA, goodVarB, goodVarC]

theorem goodMultiIndex_injective :
    Function.Injective fun p : ℕ × ℕ × ℕ =>
      goodMultiIndex p.1 p.2.1 p.2.2 := by
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
  have ha := congrArg (fun index => index goodVarA) h
  have hb := congrArg (fun index => index goodVarB) h
  have hc := congrArg (fun index => index goodVarC) h
  simp only [goodMultiIndex_a] at ha
  simp only [goodMultiIndex_b] at hb
  simp only [goodMultiIndex_c] at hc
  simp_all

theorem coeff_X_mul_index_add
    (series : GoodMvSeries) (coordinate : GoodVariable)
    (index : GoodVariable →₀ ℕ) :
    coeff ℚ (Finsupp.single coordinate 1 + index) (X coordinate * series) =
      coeff ℚ index series := by
  classical
  rw [coeff_mul]
  calc
    (∑ p ∈ Finset.antidiagonal
        (Finsupp.single coordinate 1 + index),
        coeff ℚ p.1 (X coordinate) * coeff ℚ p.2 series) =
        coeff ℚ (Finsupp.single coordinate 1) (X coordinate) *
          coeff ℚ index series := by
      apply Finset.sum_eq_single
          (Finsupp.single coordinate 1, index)
      · intro pair hmem hne
        by_cases hleft : pair.1 = Finsupp.single coordinate 1
        · have hsum := Finset.mem_antidiagonal.mp hmem
          have hright : pair.2 = index := by
            rw [hleft] at hsum
            exact add_left_cancel hsum
          exact (hne (Prod.ext hleft hright)).elim
        · rw [MvPowerSeries.coeff_X, if_neg hleft, zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim
    _ = _ := by simp [MvPowerSeries.coeff_X]

theorem coeff_X_mul_good_succ
    (series : GoodMvSeries) (x y z : ℕ) :
    coeff ℚ (goodMultiIndex (x + 1) y z) (X goodVarA * series) =
      coeff ℚ (goodMultiIndex x y z) series := by
  have hindex : goodMultiIndex (x + 1) y z =
      Finsupp.single goodVarA 1 + goodMultiIndex x y z := by
    ext coordinate
    fin_cases coordinate
    all_goals simp [goodMultiIndex, goodVarA, goodVarB, goodVarC]
    all_goals omega
  rw [hindex, coeff_X_mul_index_add]

theorem coeff_X_mul_good_succ_b
    (series : GoodMvSeries) (x y z : ℕ) :
    coeff ℚ (goodMultiIndex x (y + 1) z) (X goodVarB * series) =
      coeff ℚ (goodMultiIndex x y z) series := by
  have hindex : goodMultiIndex x (y + 1) z =
      Finsupp.single goodVarB 1 + goodMultiIndex x y z := by
    ext coordinate
    fin_cases coordinate
    all_goals simp [goodMultiIndex, goodVarA, goodVarB, goodVarC]
    all_goals omega
  rw [hindex, coeff_X_mul_index_add]

theorem coeff_X_mul_good_succ_c
    (series : GoodMvSeries) (x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y (z + 1)) (X goodVarC * series) =
      coeff ℚ (goodMultiIndex x y z) series := by
  have hindex : goodMultiIndex x y (z + 1) =
      Finsupp.single goodVarC 1 + goodMultiIndex x y z := by
    ext coordinate
    fin_cases coordinate
    all_goals simp [goodMultiIndex, goodVarA, goodVarB, goodVarC]
    all_goals omega
  rw [hindex, coeff_X_mul_index_add]

theorem coeff_XaXb_mul_good_succ
    (series : GoodMvSeries) (x y z : ℕ) :
    coeff ℚ (goodMultiIndex (x + 1) (y + 1) z)
        (X goodVarA * X goodVarB * series) =
      coeff ℚ (goodMultiIndex x y z) series := by
  rw [show X goodVarA * X goodVarB * series =
      X goodVarA * (X goodVarB * series) by ring,
    coeff_X_mul_good_succ, coeff_X_mul_good_succ_b]

theorem coeff_XaXc_mul_good_succ
    (series : GoodMvSeries) (x y z : ℕ) :
    coeff ℚ (goodMultiIndex (x + 1) y (z + 1))
        (X goodVarA * X goodVarC * series) =
      coeff ℚ (goodMultiIndex x y z) series := by
  rw [show X goodVarA * X goodVarC * series =
      X goodVarA * (X goodVarC * series) by ring,
    coeff_X_mul_good_succ, coeff_X_mul_good_succ_c]

theorem coeff_XbXc_mul_good_succ
    (series : GoodMvSeries) (x y z : ℕ) :
    coeff ℚ (goodMultiIndex x (y + 1) (z + 1))
        (X goodVarB * X goodVarC * series) =
      coeff ℚ (goodMultiIndex x y z) series := by
  rw [show X goodVarB * X goodVarC * series =
      X goodVarB * (X goodVarC * series) by ring,
    coeff_X_mul_good_succ_b, coeff_X_mul_good_succ_c]

theorem coeff_XaXbXc_mul_good_succ
    (series : GoodMvSeries) (x y z : ℕ) :
    coeff ℚ (goodMultiIndex (x + 1) (y + 1) (z + 1))
        (X goodVarA * X goodVarB * X goodVarC * series) =
      coeff ℚ (goodMultiIndex x y z) series := by
  rw [show X goodVarA * X goodVarB * X goodVarC * series =
      X goodVarA * (X goodVarB * (X goodVarC * series)) by ring,
    coeff_X_mul_good_succ, coeff_X_mul_good_succ_b,
    coeff_X_mul_good_succ_c]

theorem coeff_X_mul_good_zero
    (series : GoodMvSeries) (y z : ℕ) :
    coeff ℚ (goodMultiIndex 0 y z) (X goodVarA * series) = 0 := by
  apply (MvPowerSeries.X_dvd_iff.mp ⟨series, rfl⟩)
  simp

theorem coeff_X_mul_good_zero_b
    (series : GoodMvSeries) (x z : ℕ) :
    coeff ℚ (goodMultiIndex x 0 z) (X goodVarB * series) = 0 := by
  apply (MvPowerSeries.X_dvd_iff.mp ⟨series, rfl⟩)
  simp

theorem coeff_X_mul_good_zero_c
    (series : GoodMvSeries) (x y : ℕ) :
    coeff ℚ (goodMultiIndex x y 0) (X goodVarC * series) = 0 := by
  apply (MvPowerSeries.X_dvd_iff.mp ⟨series, rfl⟩)
  simp

noncomputable def goodResidueWeight (x y z : ℕ) : GoodMvSeries :=
  goodJacobianDetMv * goodPhiA ^ x * goodPhiB ^ y * goodPhiC ^ z

theorem goodResidueWeight_succ_a (x y z : ℕ) :
    goodResidueWeight (x + 1) y z =
      goodPhiA * goodResidueWeight x y z := by
  simp only [goodResidueWeight, pow_succ]
  ring

theorem goodResidueWeight_succ_b (x y z : ℕ) :
    goodResidueWeight x (y + 1) z =
      goodPhiB * goodResidueWeight x y z := by
  simp only [goodResidueWeight, pow_succ]
  ring

theorem goodResidueWeight_succ_c (x y z : ℕ) :
    goodResidueWeight x y (z + 1) =
      goodPhiC * goodResidueWeight x y z := by
  simp only [goodResidueWeight, pow_succ]
  ring

noncomputable def goodResidueTransform (series : GoodMvSeries) : PowerSeries ℚ :=
  PowerSeries.mk fun degree =>
    ∑ point : SimplexPoint degree,
      coeff ℚ (goodMultiIndex point.u point.v point.w)
        (series * goodResidueWeight point.u point.v point.w)

@[simp] theorem coeff_goodResidueTransform
    (series : GoodMvSeries) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodResidueTransform series) =
      ∑ point : SimplexPoint degree,
        coeff ℚ (goodMultiIndex point.u point.v point.w)
          (series * goodResidueWeight point.u point.v point.w) := by
  simp [goodResidueTransform]

def liftUEquiv (degree : ℕ) :
    SimplexPoint degree ≃ PositiveUPoint (degree + 1) :=
  (liftWEquiv degree).trans (shiftWToUEquiv (degree + 1))

def liftVEquiv (degree : ℕ) :
    SimplexPoint degree ≃ PositiveVPoint (degree + 1) :=
  (liftWEquiv degree).trans (shiftWToVEquiv (degree + 1))

theorem liftUEquiv_coordinates (degree : ℕ) (point : SimplexPoint degree) :
    (liftUEquiv degree point).1.u = point.u + 1 ∧
      (liftUEquiv degree point).1.v = point.v ∧
      (liftUEquiv degree point).1.w = point.w := by
  simp [liftUEquiv, liftWEquiv, shiftWToUEquiv]

theorem liftVEquiv_coordinates (degree : ℕ) (point : SimplexPoint degree) :
    (liftVEquiv degree point).1.u = point.u ∧
      (liftVEquiv degree point).1.v = point.v + 1 ∧
      (liftVEquiv degree point).1.w = point.w := by
  simp [liftVEquiv, liftWEquiv, shiftWToVEquiv]

theorem liftWEquiv_coordinates (degree : ℕ) (point : SimplexPoint degree) :
    (liftWEquiv degree point).1.u = point.u ∧
      (liftWEquiv degree point).1.v = point.v ∧
      (liftWEquiv degree point).1.w = point.w + 1 := by
  simp [liftWEquiv]

end BenzelProblem6Kernel
