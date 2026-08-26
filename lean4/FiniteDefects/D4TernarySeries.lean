import FiniteDefects.D4BallotFormulaKernel
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The ternary small root as a formal power series -/

namespace FiniteDefects

open Finset

def ternaryCoeff : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      ∑ pq ∈ (antidiagonal n).attach,
        (∑ ij ∈ (antidiagonal pq.1.1).attach,
          ternaryCoeff ij.1.1 * ternaryCoeff ij.1.2) *
          ternaryCoeff pq.1.2
termination_by n => n
decreasing_by
  · have hpq := Finset.mem_antidiagonal.mp pq.property
    have hij := Finset.mem_antidiagonal.mp ij.property
    omega
  · have hpq := Finset.mem_antidiagonal.mp pq.property
    have hij := Finset.mem_antidiagonal.mp ij.property
    omega
  · have hpq := Finset.mem_antidiagonal.mp pq.property
    omega

noncomputable def ternarySeries : PowerSeries ℚ :=
  PowerSeries.mk ternaryCoeff

@[simp] theorem coeff_ternarySeries (n : ℕ) :
    PowerSeries.coeff ℚ n ternarySeries = ternaryCoeff n := by
  simp [ternarySeries]

@[simp] theorem ternaryCoeff_zero : ternaryCoeff 0 = 1 := by
  rw [ternaryCoeff]

theorem coeff_mul_mul (f g h : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff ℚ n ((f * g) * h) =
      ∑ pq ∈ (antidiagonal n).attach,
        (∑ ij ∈ (antidiagonal pq.1.1).attach,
          PowerSeries.coeff ℚ ij.1.1 f *
            PowerSeries.coeff ℚ ij.1.2 g) *
          PowerSeries.coeff ℚ pq.1.2 h := by
  rw [PowerSeries.coeff_mul]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [PowerSeries.coeff_mul]
  rw [← Finset.sum_attach]

theorem ternarySeries_equation :
    ternarySeries = 1 + PowerSeries.X * ternarySeries ^ 3 := by
  ext n
  rcases n with _ | n
  · simp [ternarySeries]
  · rw [map_add]
    simp only [PowerSeries.coeff_one, if_false, map_mul,
      PowerSeries.coeff_succ_X_mul]
    rw [show ternarySeries ^ 3 =
      (ternarySeries * ternarySeries) * ternarySeries by ring]
    rw [coeff_mul_mul]
    simp only [coeff_ternarySeries]
    rw [ternaryCoeff]
    rw [if_neg (by omega), zero_add]

@[simp] theorem constantCoeff_ternarySeries :
    PowerSeries.constantCoeff ℚ ternarySeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

theorem ternarySeries_unique (S : PowerSeries ℚ)
    (hconstant : PowerSeries.constantCoeff ℚ S = 1)
    (hequation : S = 1 + PowerSeries.X * S ^ 3) :
    S = ternarySeries := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hconstant]
        simp
      · rw [show PowerSeries.coeff ℚ (n + 1) S =
          PowerSeries.coeff ℚ n (S ^ 3) by
            calc
              PowerSeries.coeff ℚ (n + 1) S =
              PowerSeries.coeff ℚ (n + 1)
                    (1 + PowerSeries.X * S ^ 3) := by rw [← hequation]
              _ = PowerSeries.coeff ℚ n (S ^ 3) := by
                simp [PowerSeries.coeff_succ_X_mul]]
        rw [show PowerSeries.coeff ℚ (n + 1) ternarySeries =
          PowerSeries.coeff ℚ n (ternarySeries ^ 3) by
            calc
              PowerSeries.coeff ℚ (n + 1) ternarySeries =
                  PowerSeries.coeff ℚ (n + 1)
                    (1 + PowerSeries.X * ternarySeries ^ 3) := by
                      rw [← ternarySeries_equation]
              _ = PowerSeries.coeff ℚ n (ternarySeries ^ 3) := by
                simp [PowerSeries.coeff_succ_X_mul]]
        rw [show S ^ 3 = (S * S) * S by ring,
          show ternarySeries ^ 3 =
            (ternarySeries * ternarySeries) * ternarySeries by ring]
        rw [coeff_mul_mul, coeff_mul_mul]
        apply Finset.sum_congr rfl
        intro pq hpq
        apply congrArg₂ (· * ·)
        · apply Finset.sum_congr rfl
          intro ij hij
          apply congrArg₂ (· * ·)
          · apply ih
            have hpq' := Finset.mem_antidiagonal.mp pq.property
            have hij' := Finset.mem_antidiagonal.mp ij.property
            omega
          · apply ih
            have hpq' := Finset.mem_antidiagonal.mp pq.property
            have hij' := Finset.mem_antidiagonal.mp ij.property
            omega
        · apply ih
          have hpq' := Finset.mem_antidiagonal.mp pq.property
          omega

end FiniteDefects
