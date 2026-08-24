import BenzelProblem6Kernel.WZBoundaryCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Factorial transport for the WZ certificate

This file attaches the checked polynomial certificate to the exact rational
factorial summand.  The large polynomial normalization remains behind the
imported `.olean`; only factorial successor identities are elaborated here.
-/

namespace BenzelProblem6Kernel

def wzPreX (m x y : ℚ) : ℚ :=
  (m + 6) * (m + 7) * wzXPolynomial m x y / (3 * (m + 4))

def wzPreY (m x y : ℚ) : ℚ :=
  (m + 6) * (m + 7) * wzYPolynomial m x y / (3 * (m + 4))

def wzCommonFactor (x y z : ℕ) : ℚ :=
  factorialQ (2 * x + y + 2) * factorialQ (2 * y + z + 2) *
      factorialQ (2 * z + x + 2) /
    (factorialQ x * factorialQ y * factorialQ (z + 1) *
      factorialQ (x + y + 3) * factorialQ (y + z + 4) *
      factorialQ (z + x + 4))

def wzIncomingX (m x y z : ℕ) : ℚ :=
  wzCommonFactor x y z * wzB₀ m x y * wzPreX m x y /
    wzLinearDenominator x y

def wzIncomingY (m x y z : ℕ) : ℚ :=
  wzCommonFactor x y z * wzB₁ m x y * wzPreY m x y /
    wzLinearDenominator x y

def wzOutgoingX (m x y z : ℕ) : ℚ :=
  wzCommonFactor x y z * wzA₀ m x y * wzPreX m (x + 1) y /
    (wzLinearDenominator x y + 2)

def wzOutgoingY (m x y z : ℕ) : ℚ :=
  wzCommonFactor x y z * wzA₁ m x y * wzPreY m x (y + 1) /
    (wzLinearDenominator x y + 1)

theorem factorialQ_succ (n : ℕ) :
    factorialQ (n + 1) = (n + 1) * factorialQ n := by
  simp only [factorialQ, Nat.factorial_succ]
  push_cast
  ring

theorem wzPre_certificate_identity (m x y : ℚ)
    (hm : m + 4 ≠ 0)
    (hD : wzLinearDenominator x y ≠ 0)
    (hD1 : wzLinearDenominator x y + 1 ≠ 0)
    (hD2 : wzLinearDenominator x y + 2 ≠ 0) :
    wzA₀ m x y * wzPreX m (x + 1) y /
          (wzLinearDenominator x y + 2) -
        wzB₀ m x y * wzPreX m x y / wzLinearDenominator x y +
        wzA₁ m x y * wzPreY m x (y + 1) /
          (wzLinearDenominator x y + 1) -
        wzB₁ m x y * wzPreY m x y / wzLinearDenominator x y =
      wzCPolynomial m x y := by
  have hcert := wz_polynomial_certificate m x y
  let bracket : ℚ :=
    wzA₀ m x y * wzXPolynomial m (x + 1) y /
        (wzLinearDenominator x y + 2) -
      wzB₀ m x y * wzXPolynomial m x y / wzLinearDenominator x y +
      wzA₁ m x y * wzYPolynomial m x (y + 1) /
        (wzLinearDenominator x y + 1) -
      wzB₁ m x y * wzYPolynomial m x y / wzLinearDenominator x y
  have hscale :
      (m + 6) * (m + 7) * bracket =
        3 * (m + 4) * wzCPolynomial m x y := by
    have hprod :
        wzLinearDenominator x y * (wzLinearDenominator x y + 1) *
            (wzLinearDenominator x y + 2) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero hD hD1) hD2
    apply mul_right_cancel₀ hprod
    calc
      ((m + 6) * (m + 7) * bracket) *
          (wzLinearDenominator x y * (wzLinearDenominator x y + 1) *
            (wzLinearDenominator x y + 2)) =
        (m + 6) * (m + 7) *
          (wzA₀ m x y * wzXPolynomial m (x + 1) y *
              wzLinearDenominator x y * (wzLinearDenominator x y + 1) -
            wzB₀ m x y * wzXPolynomial m x y *
              (wzLinearDenominator x y + 1) *
              (wzLinearDenominator x y + 2) +
            wzA₁ m x y * wzYPolynomial m x (y + 1) *
              wzLinearDenominator x y * (wzLinearDenominator x y + 2) -
            wzB₁ m x y * wzYPolynomial m x y *
              (wzLinearDenominator x y + 1) *
              (wzLinearDenominator x y + 2)) := by
          dsimp [bracket]
          field_simp [hD, hD1, hD2]
          ring
      _ = 3 * (m + 4) * wzCPolynomial m x y *
          wzLinearDenominator x y * (wzLinearDenominator x y + 1) *
          (wzLinearDenominator x y + 2) := hcert
      _ = (3 * (m + 4) * wzCPolynomial m x y) *
          (wzLinearDenominator x y * (wzLinearDenominator x y + 1) *
            (wzLinearDenominator x y + 2)) := by ring
  calc
    wzA₀ m x y * wzPreX m (x + 1) y /
          (wzLinearDenominator x y + 2) -
        wzB₀ m x y * wzPreX m x y / wzLinearDenominator x y +
        wzA₁ m x y * wzPreY m x (y + 1) /
          (wzLinearDenominator x y + 1) -
        wzB₁ m x y * wzPreY m x y / wzLinearDenominator x y =
      ((m + 6) * (m + 7) * bracket) / (3 * (m + 4)) := by
        dsimp [bracket, wzPreX, wzPreY]
        ring
    _ = wzCPolynomial m x y := by
      rw [hscale]
      field_simp [hm]

set_option maxHeartbeats 800000 in
theorem rationalKernelTerm_eq_common_current
    (m x y z : ℕ) (hm : m = x + y + z) :
    rationalKernelTerm x y z =
      wzCommonFactor x y z * wzKernelPolynomial m x y *
        wzRatioZero m x y := by
  subst m
  let top : ℚ :=
    factorialQ (2 * x + y + 2) * factorialQ (2 * y + z + 2) *
      factorialQ (2 * z + x + 2)
  let den : ℚ :=
    factorialQ x * factorialQ y * factorialQ z *
      factorialQ (x + y + 3) * factorialQ (y + z + 3) *
      factorialQ (z + x + 3)
  let extra : ℚ :=
    ((z : ℚ) + 1) * (((y + z + 3 : ℕ) : ℚ) + 1) *
      (((z + x + 3 : ℕ) : ℚ) + 1)
  have hz1 := factorialQ_succ z
  have hyz4 := factorialQ_succ (y + z + 3)
  have hzx4 := factorialQ_succ (z + x + 3)
  rw [show y + z + 3 + 1 = y + z + 4 by omega] at hyz4
  rw [show z + x + 3 + 1 = z + x + 4 by omega] at hzx4
  have hleft :
      rationalKernelTerm x y z = kernelPolynomial x y z * top / den := by
    dsimp [rationalKernelTerm, top, den]
    ring_nf
  have hcommon : wzCommonFactor x y z = top / (den * extra) := by
    dsimp [wzCommonFactor, top, den, extra]
    rw [hz1, hyz4, hzx4]
    ring
  have hkernel :
      kernelPolynomial x y z =
        wzKernelPolynomial (x + y + z : ℕ) x y := by
    simp only [kernelPolynomial, wzKernelPolynomial]
    push_cast
    ring
  have hratio :
      wzRatioZero (x + y + z : ℕ) x y = extra := by
    dsimp [wzRatioZero, extra]
    push_cast
    ring
  have hden : den ≠ 0 := by
    dsimp [den, factorialQ]
    positivity
  have hextra : extra ≠ 0 := by
    dsimp [extra]
    positivity
  rw [hleft, hcommon, ← hkernel, hratio]
  field_simp only [hden, hextra]
  ring

set_option maxHeartbeats 800000 in
theorem rationalKernelTerm_succ_eq_common_next
    (m x y z : ℕ) (hm : m = x + y + z) :
    rationalKernelTerm x y (z + 1) =
      wzCommonFactor x y z * wzKernelPolynomial (m + 1) x y *
        wzRatioOne m x y := by
  subst m
  let top : ℚ :=
    factorialQ (2 * x + y + 2) * factorialQ (2 * y + z + 2) *
      factorialQ (2 * z + x + 2)
  let den : ℚ :=
    factorialQ x * factorialQ y * factorialQ (z + 1) *
      factorialQ (x + y + 3) * factorialQ (y + z + 4) *
      factorialQ (z + x + 4)
  let extra : ℚ :=
    (((2 * y + z + 2 : ℕ) : ℚ) + 1) *
      (((2 * z + x + 2 : ℕ) : ℚ) + 1) *
      (((2 * z + x + 3 : ℕ) : ℚ) + 1)
  have hN2 := factorialQ_succ (2 * y + z + 2)
  have hN3a := factorialQ_succ (2 * z + x + 2)
  have hN3b := factorialQ_succ (2 * z + x + 3)
  have hleft :
      rationalKernelTerm x y (z + 1) =
        kernelPolynomial x y (z + 1) * (top * extra) / den := by
    dsimp [rationalKernelTerm, top, den, extra]
    rw [show 2 * y + (z + 1) + 2 = (2 * y + z + 2) + 1 by omega,
      hN2]
    rw [show 2 * (z + 1) + x + 2 = (2 * z + x + 3) + 1 by omega,
      hN3b, hN3a]
    ring_nf
  have hcommon : wzCommonFactor x y z = top / den := by
    dsimp [wzCommonFactor, top, den]
  have hkernel :
      kernelPolynomial x y (z + 1) =
        wzKernelPolynomial (x + y + z + 1 : ℕ) x y := by
    simp only [kernelPolynomial, wzKernelPolynomial]
    push_cast
    ring
  have hkernel' :
      kernelPolynomial x y (z + 1) =
        wzKernelPolynomial (((x + y + z : ℕ) : ℚ) + 1) x y := by
    simpa only [Nat.cast_add, Nat.cast_one] using hkernel
  have hratio :
      wzRatioOne (x + y + z : ℕ) x y = extra := by
    dsimp [wzRatioOne, extra]
    push_cast
    ring
  have hden : den ≠ 0 := by
    dsimp [den, factorialQ]
    positivity
  rw [hleft, hcommon, ← hkernel', hratio]
  field_simp only [hden]
  ring

theorem wz_point_recurrence (m x y z : ℕ) (hm : m = x + y + z) :
    wzLeadingCoefficient m * rationalKernelTerm x y (z + 1) -
        wzTrailingCoefficient m * rationalKernelTerm x y z =
      wzOutgoingX m x y z - wzIncomingX m x y z +
        (wzOutgoingY m x y z - wzIncomingY m x y z) := by
  rw [rationalKernelTerm_succ_eq_common_next m x y z hm,
    rationalKernelTerm_eq_common_current m x y z hm]
  have hm4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have hD : wzLinearDenominator (x : ℚ) y ≠ 0 := by
    simp [wzLinearDenominator]
    positivity
  have hD1 : wzLinearDenominator (x : ℚ) y + 1 ≠ 0 := by
    simp [wzLinearDenominator]
    positivity
  have hD2 : wzLinearDenominator (x : ℚ) y + 2 ≠ 0 := by
    simp [wzLinearDenominator]
    positivity
  have hpre := wzPre_certificate_identity (m : ℚ) x y hm4 hD hD1 hD2
  simp only [wzCPolynomial] at hpre
  simp only [wzOutgoingX, wzIncomingX, wzOutgoingY, wzIncomingY]
  calc
    wzLeadingCoefficient ↑m *
          (wzCommonFactor x y z * wzKernelPolynomial (↑m + 1) ↑x ↑y *
            wzRatioOne ↑m ↑x ↑y) -
        wzTrailingCoefficient ↑m *
          (wzCommonFactor x y z * wzKernelPolynomial ↑m ↑x ↑y *
            wzRatioZero ↑m ↑x ↑y) =
      wzCommonFactor x y z *
        (-wzTrailingCoefficient ↑m * wzKernelPolynomial ↑m ↑x ↑y *
            wzRatioZero ↑m ↑x ↑y +
          wzLeadingCoefficient ↑m * wzKernelPolynomial (↑m + 1) ↑x ↑y *
            wzRatioOne ↑m ↑x ↑y) := by ring
    _ = wzCommonFactor x y z *
        (wzA₀ ↑m ↑x ↑y * wzPreX ↑m (↑x + 1) ↑y /
              (wzLinearDenominator ↑x ↑y + 2) -
          wzB₀ ↑m ↑x ↑y * wzPreX ↑m ↑x ↑y /
              wzLinearDenominator ↑x ↑y +
          wzA₁ ↑m ↑x ↑y * wzPreY ↑m ↑x (↑y + 1) /
              (wzLinearDenominator ↑x ↑y + 1) -
          wzB₁ ↑m ↑x ↑y * wzPreY ↑m ↑x ↑y /
              wzLinearDenominator ↑x ↑y) := by rw [hpre]
    _ = wzCommonFactor x y z * wzA₀ ↑m ↑x ↑y *
            wzPreX ↑m (↑x + 1) ↑y / (wzLinearDenominator ↑x ↑y + 2) -
          wzCommonFactor x y z * wzB₀ ↑m ↑x ↑y * wzPreX ↑m ↑x ↑y /
            wzLinearDenominator ↑x ↑y +
        (wzCommonFactor x y z * wzA₁ ↑m ↑x ↑y *
            wzPreY ↑m ↑x (↑y + 1) / (wzLinearDenominator ↑x ↑y + 1) -
          wzCommonFactor x y z * wzB₁ ↑m ↑x ↑y * wzPreY ↑m ↑x ↑y /
            wzLinearDenominator ↑x ↑y) := by ring

end BenzelProblem6Kernel
