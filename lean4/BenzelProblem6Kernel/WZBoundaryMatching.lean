import BenzelProblem6Kernel.WZBoundaryFlux

/-!
# Matching the last interior edges to the boundary flux
-/

namespace BenzelProblem6Kernel

set_option maxHeartbeats 600000 in
theorem wzCommonFactor_boundary_shiftX (m x y : ℕ) (hm : m = x + y) :
    wzCommonFactor x y 0 * wzA₀ m x y =
      wzBoundaryCommonFactor (x + 1) y * wzB₀ m (x + 1) y := by
  subst m
  have hN1 := factorialQ_add_two (2 * x + y + 2)
  have hN2 := factorialQ_succ (2 * y + 1)
  have hx2 := factorialQ_add_two x
  have hxsucc := factorialQ_succ x
  have hxy := factorialQ_succ (x + y + 3)
  have hy := factorialQ_succ (y + 3)
  have hdenCurrent :
      factorialQ x * factorialQ y * factorialQ (0 + 1) *
          factorialQ (x + y + 3) * factorialQ (y + 0 + 4) *
          factorialQ (0 + x + 4) ≠ 0 := by
    repeat' apply mul_ne_zero
    all_goals exact factorialQ_ne_zero _
  have hdenBoundary :
      factorialQ (x + 1) * factorialQ y * factorialQ 0 *
          factorialQ (x + 1 + y + 3) * factorialQ (y + 3) *
          factorialQ (x + 1 + 3) ≠ 0 := by
    repeat' apply mul_ne_zero
    all_goals exact factorialQ_ne_zero _
  have hA :
      wzA₀ (x + y : ℕ) x y =
        (((y + 3 : ℕ) : ℚ) + 1) *
          (((2 * x + y + 2 : ℕ) : ℚ) + 1) *
          (((2 * x + y + 2 : ℕ) : ℚ) + 2) := by
    simp [wzA₀]
    ring
  have hB :
      wzB₀ (x + y : ℕ) (x + 1) y =
        ((x : ℚ) + 1) * (((x + y + 3 : ℕ) : ℚ) + 1) *
          ((x : ℚ) + 2) * (((2 * y + 1 : ℕ) : ℚ) + 1) := by
    simp only [wzB₀]
    push_cast
    ring
  simp only [wzCommonFactor, wzBoundaryCommonFactor]
  rw [hA, hB]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_eq_div_iff hdenCurrent hdenBoundary).2
  rw [show 2 * (x + 1) + y + 2 = (2 * x + y + 2) + 2 by omega,
    hN1]
  rw [show 2 * y + 2 = (2 * y + 1) + 1 by omega, hN2]
  rw [show 2 * 0 + x + 2 = x + 2 by omega, hx2]
  rw [hxsucc]
  rw [show x + 1 + y + 3 = (x + y + 3) + 1 by omega, hxy]
  rw [show y + 0 + 4 = (y + 3) + 1 by omega, hy]
  norm_num [factorialQ]
  rw [show x + 1 + 3 = x + 4 by omega]
  ac_rfl

theorem wzOutgoingX_eq_boundaryIncomingX
    (m x y : ℕ) (hm : m = x + y) :
    wzOutgoingX m x y 0 = wzBoundaryIncomingX m (x + 1) y := by
  have hcore := wzCommonFactor_boundary_shiftX m x y hm
  simp only [wzOutgoingX, wzBoundaryIncomingX]
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
theorem wzCommonFactor_boundary_shiftY (m x y : ℕ) (hm : m = x + y) :
    wzCommonFactor x y 0 * wzA₁ m x y =
      wzBoundaryCommonFactor x (y + 1) * wzB₁ m x (y + 1) := by
  subst m
  have hN1 := factorialQ_succ (2 * x + y + 2)
  have hN2 := factorialQ_succ (2 * y + 2)
  have hx2 := factorialQ_add_two x
  have hysucc := factorialQ_succ y
  have hxy := factorialQ_succ (x + y + 3)
  have hx3 := factorialQ_succ (x + 3)
  have hdenCurrent :
      factorialQ x * factorialQ y * factorialQ (0 + 1) *
          factorialQ (x + y + 3) * factorialQ (y + 0 + 4) *
          factorialQ (0 + x + 4) ≠ 0 := by
    repeat' apply mul_ne_zero
    all_goals exact factorialQ_ne_zero _
  have hdenBoundary :
      factorialQ x * factorialQ (y + 1) * factorialQ 0 *
          factorialQ (x + y + 1 + 3) * factorialQ (y + 1 + 3) *
          factorialQ (x + 3) ≠ 0 := by
    repeat' apply mul_ne_zero
    all_goals exact factorialQ_ne_zero _
  have hA :
      wzA₁ (x + y : ℕ) x y =
        (((x + 3 : ℕ) : ℚ) + 1) *
          (((2 * x + y + 2 : ℕ) : ℚ) + 1) *
          (((2 * y + 2 : ℕ) : ℚ) + 1) := by
    simp only [wzA₁]
    push_cast
    ring
  have hB :
      wzB₁ (x + y : ℕ) x (y + 1) =
        ((y : ℚ) + 1) * (((x + y + 3 : ℕ) : ℚ) + 1) *
          ((x : ℚ) + 2) * ((x : ℚ) + 1) := by
    simp only [wzB₁]
    push_cast
    ring
  simp only [wzCommonFactor, wzBoundaryCommonFactor]
  rw [hA, hB]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_eq_div_iff hdenCurrent hdenBoundary).2
  rw [show 2 * x + (y + 1) + 2 = (2 * x + y + 2) + 1 by omega,
    hN1]
  rw [show 2 * (y + 1) + 1 = (2 * y + 2) + 1 by omega, hN2]
  rw [show 2 * 0 + x + 2 = x + 2 by omega, hx2]
  rw [hysucc]
  rw [show x + y + 1 + 3 = (x + y + 3) + 1 by omega, hxy]
  rw [show 0 + x + 4 = (x + 3) + 1 by omega, hx3]
  norm_num [factorialQ]
  rw [show y + 0 + 4 = y + 4 by omega,
    show y + 1 + 3 = y + 4 by omega]
  ac_rfl

theorem wzOutgoingY_eq_boundaryIncomingY
    (m x y : ℕ) (hm : m = x + y) :
    wzOutgoingY m x y 0 = wzBoundaryIncomingY m x (y + 1) := by
  have hcore := wzCommonFactor_boundary_shiftY m x y hm
  simp only [wzOutgoingY, wzBoundaryIncomingY]
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
