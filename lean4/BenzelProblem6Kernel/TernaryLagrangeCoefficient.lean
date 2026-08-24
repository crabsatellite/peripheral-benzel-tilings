import BenzelProblem6Kernel.TernarySeriesEquation
import BenzelProblem6Kernel.PathModelRationalKernel

/-!
# The Lagrange coefficient for powers of the ternary series

For `T = 1 + X T^3`, multiplication by the defining equation gives
`T^(r+1) = T^r + X T^(r+3)`.  The Raney/Lagrange coefficient satisfies the
same two-dimensional recurrence, which proves the exact coefficient formula
without an analytic convergence assumption.
-/

namespace BenzelProblem6Kernel

open PowerSeries

def ternaryLagrangeCoefficient (degree exponent : ℕ) : ℚ :=
  if degree = 0 ∧ exponent = 0 then 1 else
    (exponent : ℚ) * factorialQ (3 * degree + exponent - 1) /
      (factorialQ degree * factorialQ (2 * degree + exponent))

theorem factorialQ_succ' (n : ℕ) :
    factorialQ (n + 1) = (n + 1 : ℕ) * factorialQ n := by
  simp only [factorialQ, Nat.factorial_succ]
  push_cast
  ring

theorem ternaryLagrangeCoefficient_zero_zero :
    ternaryLagrangeCoefficient 0 0 = 1 := by
  simp [ternaryLagrangeCoefficient]

theorem ternaryLagrangeCoefficient_positive_zero (degree : ℕ) :
    ternaryLagrangeCoefficient (degree + 1) 0 = 0 := by
  simp [ternaryLagrangeCoefficient]

theorem ternaryLagrangeCoefficient_zero_succ (exponent : ℕ) :
    ternaryLagrangeCoefficient 0 (exponent + 1) = 1 := by
  simp only [ternaryLagrangeCoefficient, Nat.succ_ne_zero, and_false,
    if_false]
  rw [show 3 * 0 + (exponent + 1) - 1 = exponent by omega,
    show 2 * 0 + (exponent + 1) = exponent + 1 by omega]
  rw [factorialQ_succ']
  field_simp [factorialQ_ne_zero]
  simp [factorialQ]

theorem ternaryLagrangeCoefficient_recurrence (degree exponent : ℕ) :
    ternaryLagrangeCoefficient (degree + 1) (exponent + 1) =
      ternaryLagrangeCoefficient (degree + 1) exponent +
        ternaryLagrangeCoefficient degree (exponent + 3) := by
  simp only [ternaryLagrangeCoefficient, Nat.succ_ne_zero, and_false,
    if_false]
  have h₀ : 3 * (degree + 1) + (exponent + 1) - 1 =
      3 * degree + exponent + 3 := by omega
  have h₁ : 3 * (degree + 1) + exponent - 1 =
      3 * degree + exponent + 2 := by omega
  have h₂ : 3 * degree + (exponent + 3) - 1 =
      3 * degree + exponent + 2 := by omega
  have h₃ : 2 * (degree + 1) + (exponent + 1) =
      2 * degree + exponent + 3 := by omega
  have h₄ : 2 * (degree + 1) + exponent =
      2 * degree + exponent + 2 := by omega
  have h₅ : 2 * degree + (exponent + 3) =
      2 * degree + exponent + 3 := by omega
  rw [h₀, h₁, h₂, h₃, h₄, h₅]
  rw [show 3 * degree + exponent + 3 =
      (3 * degree + exponent + 2) + 1 by omega]
  rw [show 2 * degree + exponent + 3 =
      (2 * degree + exponent + 2) + 1 by omega]
  rw [factorialQ_succ' (3 * degree + exponent + 2),
    factorialQ_succ' degree,
    factorialQ_succ' (2 * degree + exponent + 2)]
  field_simp [factorialQ_ne_zero]
  ring

theorem ternarySeries_pow_succ_identity (exponent : ℕ) :
    ternarySeries ^ (exponent + 1) =
      ternarySeries ^ exponent + X * ternarySeries ^ (exponent + 3) := by
  calc
    ternarySeries ^ (exponent + 1) =
        ternarySeries ^ exponent * ternarySeries := by rw [pow_succ]
    _ = ternarySeries ^ exponent *
        (1 + X * ternarySeries ^ 3) := by rw [← ternarySeries_equation]
    _ = ternarySeries ^ exponent + X * ternarySeries ^ (exponent + 3) := by
      ring

theorem coeff_ternarySeries_pow_succ (degree exponent : ℕ) :
    coeff ℚ (degree + 1) (ternarySeries ^ (exponent + 1)) =
      coeff ℚ (degree + 1) (ternarySeries ^ exponent) +
        coeff ℚ degree (ternarySeries ^ (exponent + 3)) := by
  rw [ternarySeries_pow_succ_identity, map_add]
  congr 1
  rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp]
  rw [coeff_X_pow_mul]

theorem ternarySeries_constantCoeff_pow (exponent : ℕ) :
    coeff ℚ 0 (ternarySeries ^ exponent) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow,
    ternarySeries_constantCoeff]
  simp

theorem coeff_ternarySeries_pow_eq_lagrange :
    ∀ degree exponent : ℕ,
      coeff ℚ degree (ternarySeries ^ exponent) =
        ternaryLagrangeCoefficient degree exponent := by
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree ih =>
      intro exponent
      cases degree with
      | zero =>
          cases exponent with
          | zero =>
              simp [ternaryLagrangeCoefficient_zero_zero]
          | succ exponent =>
              rw [ternarySeries_constantCoeff_pow,
                ternaryLagrangeCoefficient_zero_succ]
      | succ degree =>
          induction exponent with
          | zero =>
              rw [pow_zero]
              simp [ternaryLagrangeCoefficient_positive_zero]
          | succ exponent hexponent =>
              rw [coeff_ternarySeries_pow_succ,
                hexponent, ih degree (by omega) (exponent + 3),
                ternaryLagrangeCoefficient_recurrence]

theorem coeff_ternarySeries_pow_nine (degree : ℕ) :
    coeff ℚ degree (ternarySeries ^ 9) =
      (9 : ℚ) / (2 * degree + 9) * (3 * degree + 8).choose degree := by
  rw [coeff_ternarySeries_pow_eq_lagrange]
  simp only [ternaryLagrangeCoefficient, OfNat.ofNat, Nat.reduceEqDiff,
    and_false, if_false]
  have hchoose := choose_cast_eq_factorial_ratio
      (3 * degree + 8) degree (by omega)
  rw [show 3 * degree + 8 - degree = 2 * degree + 8 by omega] at hchoose
  have htop : 3 * degree + 9 - 1 = 3 * degree + 8 := by omega
  rw [htop, hchoose]
  have hbottom := factorialQ_succ' (2 * degree + 8)
  rw [show 2 * degree + 8 + 1 = 2 * degree + 9 by omega] at hbottom
  rw [hbottom]
  field_simp [factorialQ_ne_zero]
  ring

end BenzelProblem6Kernel
