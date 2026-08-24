import BenzelProblem6Kernel.GoodResidueKernel

/-!
# Coefficients of separated coordinate powers
-/

namespace BenzelProblem6Kernel

open MvPowerSeries

theorem coeff_good_power_c :
    ∀ power x y z : ℕ,
      coeff ℚ (goodMultiIndex x y z) ((1 + X goodVarC) ^ power) =
        if x = 0 ∧ y = 0 then (power.choose z : ℚ) else 0 := by
  intro power
  induction power with
  | zero =>
      intro x y z
      rw [pow_zero, MvPowerSeries.coeff_one]
      by_cases hx : x = 0
      · subst x
        by_cases hy : y = 0
        · subst y
          cases z <;>
            simp [goodMultiIndex, goodVarA, goodVarB, goodVarC]
        · have hindex : goodMultiIndex 0 y z ≠ 0 := by
            intro h
            have := congrArg (fun index => index goodVarB) h
            simp at this
            exact hy this
          simp [hy, hindex]
      · have hindex : goodMultiIndex x y z ≠ 0 := by
          intro h
          have := congrArg (fun index => index goodVarA) h
          simp at this
          exact hx this
        simp [hx, hindex]
  | succ power ih =>
      intro x y z
      rw [pow_succ]
      rw [show ((1 : GoodMvSeries) + X goodVarC) ^ power *
            ((1 : GoodMvSeries) + X goodVarC) =
          ((1 : GoodMvSeries) + X goodVarC) ^ power +
            X goodVarC * ((1 : GoodMvSeries) + X goodVarC) ^ power by ring,
        map_add]
      cases z with
      | zero =>
          rw [coeff_X_mul_good_zero_c, ih]
          by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
            simp [hx, hy]
      | succ z =>
          rw [coeff_X_mul_good_succ_c, ih, ih]
          by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
            simp [hx, hy, Nat.choose]
          all_goals ring

theorem coeff_good_powers_bc :
    ∀ powerB powerC x y z : ℕ,
      coeff ℚ (goodMultiIndex x y z)
          ((1 + X goodVarB) ^ powerB *
            (1 + X goodVarC) ^ powerC) =
        if x = 0 then
          (powerB.choose y : ℚ) * powerC.choose z else 0 := by
  intro powerB
  induction powerB with
  | zero =>
      intro powerC x y z
      cases x with
      | zero =>
          cases y <;> simp [coeff_good_power_c]
      | succ x => simp [coeff_good_power_c]
  | succ powerB ih =>
      intro powerC x y z
      rw [pow_succ]
      rw [show (((1 : GoodMvSeries) + X goodVarB) ^ powerB *
            ((1 : GoodMvSeries) + X goodVarB)) *
          ((1 : GoodMvSeries) + X goodVarC) ^ powerC =
          ((1 : GoodMvSeries) + X goodVarB) ^ powerB *
              ((1 : GoodMvSeries) + X goodVarC) ^ powerC +
            X goodVarB * (((1 : GoodMvSeries) + X goodVarB) ^ powerB *
              ((1 : GoodMvSeries) + X goodVarC) ^ powerC) by ring,
        map_add]
      cases y with
      | zero =>
          rw [coeff_X_mul_good_zero_b, ih]
          by_cases hx : x = 0 <;> simp [hx]
      | succ y =>
          rw [coeff_X_mul_good_succ_b, ih, ih]
          by_cases hx : x = 0
          all_goals simp [hx, Nat.choose]
          all_goals ring

theorem coeff_separated_good_powers :
    ∀ powerA powerB powerC x y z : ℕ,
      coeff ℚ (goodMultiIndex x y z)
          ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB *
            (1 + X goodVarC) ^ powerC) =
        (powerA.choose x : ℚ) * powerB.choose y * powerC.choose z := by
  intro powerA
  induction powerA with
  | zero =>
      intro powerB powerC x y z
      cases x <;> simp [coeff_good_powers_bc]
  | succ powerA ih =>
      intro powerB powerC x y z
      rw [pow_succ]
      rw [show (((1 : GoodMvSeries) + X goodVarA) ^ powerA *
            ((1 : GoodMvSeries) + X goodVarA)) *
            ((1 : GoodMvSeries) + X goodVarB) ^ powerB *
            ((1 : GoodMvSeries) + X goodVarC) ^ powerC =
          ((1 : GoodMvSeries) + X goodVarA) ^ powerA *
              ((1 : GoodMvSeries) + X goodVarB) ^ powerB *
              ((1 : GoodMvSeries) + X goodVarC) ^ powerC +
            X goodVarA * (((1 : GoodMvSeries) + X goodVarA) ^ powerA *
              ((1 : GoodMvSeries) + X goodVarB) ^ powerB *
              ((1 : GoodMvSeries) + X goodVarC) ^ powerC) by ring,
        map_add]
      cases x with
      | zero =>
          rw [coeff_X_mul_good_zero, ih]
          simp
      | succ x =>
          rw [coeff_X_mul_good_succ, ih, ih]
          simp [Nat.choose]
          ring

theorem coeff_Xa_separated_good_powers
    (powerA powerB powerC x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z)
        (X goodVarA * ((1 + X goodVarA) ^ powerA *
          (1 + X goodVarB) ^ powerB *
          (1 + X goodVarC) ^ powerC)) =
      (choosePred powerA x : ℚ) * powerB.choose y * powerC.choose z := by
  cases x with
  | zero => simp [coeff_X_mul_good_zero, choosePred]
  | succ x =>
      rw [coeff_X_mul_good_succ, coeff_separated_good_powers]
      rfl

theorem coeff_Xb_separated_good_powers
    (powerA powerB powerC x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z)
        (X goodVarB * ((1 + X goodVarA) ^ powerA *
          (1 + X goodVarB) ^ powerB *
          (1 + X goodVarC) ^ powerC)) =
      (powerA.choose x : ℚ) * choosePred powerB y * powerC.choose z := by
  cases y with
  | zero => simp [coeff_X_mul_good_zero_b, choosePred]
  | succ y =>
      rw [coeff_X_mul_good_succ_b, coeff_separated_good_powers]
      rfl

theorem coeff_Xc_separated_good_powers
    (powerA powerB powerC x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z)
        (X goodVarC * ((1 + X goodVarA) ^ powerA *
          (1 + X goodVarB) ^ powerB *
          (1 + X goodVarC) ^ powerC)) =
      (powerA.choose x : ℚ) * powerB.choose y * choosePred powerC z := by
  cases z with
  | zero => simp [coeff_X_mul_good_zero_c, choosePred]
  | succ z =>
      rw [coeff_X_mul_good_succ_c, coeff_separated_good_powers]
      rfl

theorem coeff_XaXb_separated_good_powers
    (powerA powerB powerC x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z)
        (X goodVarA * X goodVarB * ((1 + X goodVarA) ^ powerA *
          (1 + X goodVarB) ^ powerB *
          (1 + X goodVarC) ^ powerC)) =
      (choosePred powerA x : ℚ) * choosePred powerB y * powerC.choose z := by
  cases x with
  | zero =>
      have hzero : coeff ℚ (goodMultiIndex 0 y z)
          (X goodVarA * X goodVarB * ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC)) = 0 := by
        apply (MvPowerSeries.X_dvd_iff.mp
          ⟨X goodVarB * ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
        simp
      rw [hzero]
      simp [choosePred]
  | succ x =>
      cases y with
      | zero =>
          have hzero : coeff ℚ (goodMultiIndex (x + 1) 0 z)
              (X goodVarA * X goodVarB * ((1 + X goodVarA) ^ powerA *
                (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC)) = 0 := by
            apply ((MvPowerSeries.X_dvd_iff (s := goodVarB)).mp
              ⟨X goodVarA * ((1 + X goodVarA) ^ powerA *
                (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
            simp
          rw [hzero]
          simp [choosePred]
      | succ y =>
          rw [coeff_XaXb_mul_good_succ, coeff_separated_good_powers]
          rfl

theorem coeff_XaXc_separated_good_powers
    (powerA powerB powerC x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z)
        (X goodVarA * X goodVarC * ((1 + X goodVarA) ^ powerA *
          (1 + X goodVarB) ^ powerB *
          (1 + X goodVarC) ^ powerC)) =
      (choosePred powerA x : ℚ) * powerB.choose y * choosePred powerC z := by
  cases x with
  | zero =>
      have hzero : coeff ℚ (goodMultiIndex 0 y z)
          (X goodVarA * X goodVarC * ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC)) = 0 := by
        apply (MvPowerSeries.X_dvd_iff.mp
          ⟨X goodVarC * ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
        simp
      rw [hzero]
      simp [choosePred]
  | succ x =>
      cases z with
      | zero =>
          have hzero : coeff ℚ (goodMultiIndex (x + 1) y 0)
              (X goodVarA * X goodVarC * ((1 + X goodVarA) ^ powerA *
                (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC)) = 0 := by
            apply ((MvPowerSeries.X_dvd_iff (s := goodVarC)).mp
              ⟨X goodVarA * ((1 + X goodVarA) ^ powerA *
                (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
            simp
          rw [hzero]
          simp [choosePred]
      | succ z =>
          rw [coeff_XaXc_mul_good_succ, coeff_separated_good_powers]
          rfl

theorem coeff_XbXc_separated_good_powers
    (powerA powerB powerC x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z)
        (X goodVarB * X goodVarC * ((1 + X goodVarA) ^ powerA *
          (1 + X goodVarB) ^ powerB *
          (1 + X goodVarC) ^ powerC)) =
      (powerA.choose x : ℚ) * choosePred powerB y * choosePred powerC z := by
  cases y with
  | zero =>
      have hzero : coeff ℚ (goodMultiIndex x 0 z)
          (X goodVarB * X goodVarC * ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC)) = 0 := by
        apply ((MvPowerSeries.X_dvd_iff (s := goodVarB)).mp
          ⟨X goodVarC * ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
        simp
      rw [hzero]
      simp [choosePred]
  | succ y =>
      cases z with
      | zero =>
          have hzero : coeff ℚ (goodMultiIndex x (y + 1) 0)
              (X goodVarB * X goodVarC * ((1 + X goodVarA) ^ powerA *
                (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC)) = 0 := by
            apply ((MvPowerSeries.X_dvd_iff (s := goodVarC)).mp
              ⟨X goodVarB * ((1 + X goodVarA) ^ powerA *
                (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
            simp
          rw [hzero]
          simp [choosePred]
      | succ z =>
          rw [coeff_XbXc_mul_good_succ, coeff_separated_good_powers]
          rfl

theorem coeff_XaXbXc_separated_good_powers
    (powerA powerB powerC x y z : ℕ) :
    coeff ℚ (goodMultiIndex x y z)
        (X goodVarA * X goodVarB * X goodVarC *
          ((1 + X goodVarA) ^ powerA * (1 + X goodVarB) ^ powerB *
            (1 + X goodVarC) ^ powerC)) =
      (choosePred powerA x : ℚ) * choosePred powerB y *
        choosePred powerC z := by
  cases x with
  | zero =>
      have hzero : coeff ℚ (goodMultiIndex 0 y z)
          (X goodVarA * X goodVarB * X goodVarC *
            ((1 + X goodVarA) ^ powerA * (1 + X goodVarB) ^ powerB *
              (1 + X goodVarC) ^ powerC)) = 0 := by
        apply (MvPowerSeries.X_dvd_iff.mp
          ⟨X goodVarB * X goodVarC * ((1 + X goodVarA) ^ powerA *
            (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
        simp
      rw [hzero]
      simp [choosePred]
  | succ x =>
      cases y with
      | zero =>
          have hzero : coeff ℚ (goodMultiIndex (x + 1) 0 z)
              (X goodVarA * X goodVarB * X goodVarC *
                ((1 + X goodVarA) ^ powerA * (1 + X goodVarB) ^ powerB *
                  (1 + X goodVarC) ^ powerC)) = 0 := by
            apply ((MvPowerSeries.X_dvd_iff (s := goodVarB)).mp
              ⟨X goodVarA * X goodVarC * ((1 + X goodVarA) ^ powerA *
                (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
            simp
          rw [hzero]
          simp [choosePred]
      | succ y =>
          cases z with
          | zero =>
              have hzero : coeff ℚ (goodMultiIndex (x + 1) (y + 1) 0)
                  (X goodVarA * X goodVarB * X goodVarC *
                    ((1 + X goodVarA) ^ powerA * (1 + X goodVarB) ^ powerB *
                      (1 + X goodVarC) ^ powerC)) = 0 := by
                apply ((MvPowerSeries.X_dvd_iff (s := goodVarC)).mp
                  ⟨X goodVarA * X goodVarB * ((1 + X goodVarA) ^ powerA *
                    (1 + X goodVarB) ^ powerB * (1 + X goodVarC) ^ powerC), by ring⟩)
                simp
              rw [hzero]
              simp [choosePred]
          | succ z =>
              rw [coeff_XaXbXc_mul_good_succ,
                coeff_separated_good_powers]
              rfl

end BenzelProblem6Kernel
