import BenzelProblem6Kernel.WZFactorialTransport

/-!
# Matching adjacent WZ fluxes

The pointwise certificate is written with outgoing and incoming edge terms.
This file proves that the two descriptions of every interior simplex edge are
identical, so their finite sums telescope without an analytic extension.
-/

namespace BenzelProblem6Kernel

theorem factorialQ_add_two (n : ℕ) :
    factorialQ (n + 2) = (n + 2) * (n + 1) * factorialQ n := by
  rw [show n + 2 = (n + 1) + 1 by omega, factorialQ_succ,
    factorialQ_succ]
  push_cast
  ring

set_option maxHeartbeats 600000 in
theorem wzCommonFactor_shiftX
    (m x y z : ℕ) (hm : m = x + y + z) (hz : 0 < z) :
    wzCommonFactor x y z * wzA₀ m x y =
      wzCommonFactor (x + 1) y (z - 1) * wzB₀ m (x + 1) y := by
  rcases z with _ | k
  · omega
  · subst m
    have hN1 := factorialQ_add_two (2 * x + y + 2)
    have hN2 := factorialQ_succ (2 * y + k + 2)
    have hN3 := factorialQ_succ (2 * k + x + 3)
    have hxsucc := factorialQ_succ x
    have hksucc := factorialQ_succ (k + 1)
    have hxysucc := factorialQ_succ (x + y + 3)
    have hyksucc := factorialQ_succ (y + k + 4)
    have hdenCurrent :
        factorialQ x * factorialQ y * factorialQ (k + 1 + 1) *
            factorialQ (x + y + 3) * factorialQ (y + (k + 1) + 4) *
            factorialQ (k + 1 + x + 4) ≠ 0 := by
      repeat' apply mul_ne_zero
      all_goals exact factorialQ_ne_zero _
    have hdenNext :
        factorialQ (x + 1) * factorialQ y * factorialQ (k + 1) *
            factorialQ (x + 1 + y + 3) * factorialQ (y + k + 4) *
            factorialQ (k + (x + 1) + 4) ≠ 0 := by
      repeat' apply mul_ne_zero
      all_goals exact factorialQ_ne_zero _
    have hA :
        wzA₀ (x + y + (k + 1) : ℕ) x y =
          (((y + k + 4 : ℕ) : ℚ) + 1) *
            (((2 * x + y + 2 : ℕ) : ℚ) + 1) *
            (((2 * x + y + 2 : ℕ) : ℚ) + 2) *
            (((k + 1 : ℕ) : ℚ) + 1) := by
      simp only [wzA₀]
      push_cast
      ring
    have hB :
        wzB₀ (x + y + (k + 1) : ℕ) (x + 1) y =
          ((x : ℚ) + 1) * (((x + y + 3 : ℕ) : ℚ) + 1) *
            (((2 * k + x + 3 : ℕ) : ℚ) + 1) *
            (((2 * y + k + 2 : ℕ) : ℚ) + 1) := by
      simp only [wzB₀]
      push_cast
      ring
    simp only [wzCommonFactor]
    rw [hA, hB]
    push_cast
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_eq_div_iff hdenCurrent hdenNext).2
    rw [show 2 * (x + 1) + y + 2 = (2 * x + y + 2) + 2 by omega,
      hN1]
    rw [show 2 * y + (k + 1) + 2 = (2 * y + k + 2) + 1 by omega,
      hN2]
    rw [show 2 * (k + 1) + x + 2 = (2 * k + x + 3) + 1 by omega,
      hN3]
    rw [hxsucc, hksucc]
    rw [show x + 1 + y + 3 = (x + y + 3) + 1 by omega, hxysucc]
    rw [show y + (k + 1) + 4 = (y + k + 4) + 1 by omega,
      hyksucc]
    rw [show 2 * k + (x + 1) + 2 = 2 * k + x + 3 by omega]
    rw [show k + (x + 1) + 4 = k + x + 5 by omega,
      show k + 1 + x + 4 = k + x + 5 by omega]
    push_cast
    ac_rfl

theorem wzOutgoingX_eq_nextIncomingX
    (m x y z : ℕ) (hm : m = x + y + z) (hz : 0 < z) :
    wzOutgoingX m x y z = wzIncomingX m (x + 1) y (z - 1) := by
  have hcore := wzCommonFactor_shiftX m x y z hm hz
  simp only [wzOutgoingX, wzIncomingX]
  rw [hcore]
  have hDshift :
      wzLinearDenominator ((x + 1 : ℕ) : ℚ) y =
        wzLinearDenominator x y + 2 := by
    simp [wzLinearDenominator]
    ring
  rw [hDshift]
  push_cast
  ring_nf

set_option maxHeartbeats 600000 in
theorem wzCommonFactor_shiftY
    (m x y z : ℕ) (hm : m = x + y + z) (hz : 0 < z) :
    wzCommonFactor x y z * wzA₁ m x y =
      wzCommonFactor x (y + 1) (z - 1) * wzB₁ m x (y + 1) := by
  rcases z with _ | k
  · omega
  · subst m
    have hN1 := factorialQ_succ (2 * x + y + 2)
    have hN2 := factorialQ_succ (2 * y + k + 3)
    have hN3 := factorialQ_add_two (2 * k + x + 2)
    have hysucc := factorialQ_succ y
    have hksucc := factorialQ_succ (k + 1)
    have hxysucc := factorialQ_succ (x + y + 3)
    have hkxsucc := factorialQ_succ (k + x + 4)
    have hdenCurrent :
        factorialQ x * factorialQ y * factorialQ (k + 1 + 1) *
            factorialQ (x + y + 3) * factorialQ (y + (k + 1) + 4) *
            factorialQ (k + 1 + x + 4) ≠ 0 := by
      repeat' apply mul_ne_zero
      all_goals exact factorialQ_ne_zero _
    have hdenNext :
        factorialQ x * factorialQ (y + 1) * factorialQ (k + 1) *
            factorialQ (x + (y + 1) + 3) * factorialQ (y + 1 + k + 4) *
            factorialQ (k + x + 4) ≠ 0 := by
      repeat' apply mul_ne_zero
      all_goals exact factorialQ_ne_zero _
    have hA :
        wzA₁ (x + y + (k + 1) : ℕ) x y =
          (((x + k + 4 : ℕ) : ℚ) + 1) *
            (((2 * x + y + 2 : ℕ) : ℚ) + 1) *
            (((2 * y + k + 3 : ℕ) : ℚ) + 1) *
            (((k + 1 : ℕ) : ℚ) + 1) := by
      simp only [wzA₁]
      push_cast
      ring
    have hB :
        wzB₁ (x + y + (k + 1) : ℕ) x (y + 1) =
          ((y : ℚ) + 1) * (((x + y + 3 : ℕ) : ℚ) + 1) *
            (((2 * k + x + 2 : ℕ) : ℚ) + 2) *
            (((2 * k + x + 2 : ℕ) : ℚ) + 1) := by
      simp only [wzB₁]
      push_cast
      ring
    simp only [wzCommonFactor]
    rw [hA, hB]
    push_cast
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_eq_div_iff hdenCurrent hdenNext).2
    rw [show 2 * x + (y + 1) + 2 = (2 * x + y + 2) + 1 by omega,
      hN1]
    rw [show 2 * (y + 1) + k + 2 = (2 * y + k + 3) + 1 by omega,
      hN2]
    rw [show 2 * (k + 1) + x + 2 = (2 * k + x + 2) + 2 by omega,
      hN3]
    rw [hysucc, hksucc]
    rw [show x + (y + 1) + 3 = (x + y + 3) + 1 by omega, hxysucc]
    rw [show k + 1 + x + 4 = (k + x + 4) + 1 by omega, hkxsucc]
    rw [show y + 1 + k + 4 = y + k + 5 by omega,
      show y + (k + 1) + 4 = y + k + 5 by omega]
    rw [show 2 * y + (k + 1) + 2 = 2 * y + k + 3 by omega]
    rw [show k + x + 4 = k + x + 4 by rfl]
    push_cast
    ac_rfl

theorem wzOutgoingY_eq_nextIncomingY
    (m x y z : ℕ) (hm : m = x + y + z) (hz : 0 < z) :
    wzOutgoingY m x y z = wzIncomingY m x (y + 1) (z - 1) := by
  have hcore := wzCommonFactor_shiftY m x y z hm hz
  simp only [wzOutgoingY, wzIncomingY]
  rw [hcore]
  have hDshift :
      wzLinearDenominator x ((y + 1 : ℕ) : ℚ) =
        wzLinearDenominator x y + 1 := by
    simp [wzLinearDenominator]
    ring
  rw [hDshift]
  push_cast
  ring_nf

end BenzelProblem6Kernel
