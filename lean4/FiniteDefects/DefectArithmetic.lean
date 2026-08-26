import FiniteDefects.OwnerBoundary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Kernel arithmetic of the defect-count theorem -/

namespace FiniteDefects

theorem defects_d3k
    (a k bones wrongPhaseStones threeOwnerBones : ℕ)
    (hbone : (bones : ℚ) = 3 * k * (a - 2 * k))
    (henergy :
      (bones : ℚ) +
          3 * ((wrongPhaseStones : ℚ) + threeOwnerBones) =
        3 * k * (a - (3 * k + 1 : ℚ) / 2)) :
    wrongPhaseStones + threeOwnerBones = k.choose 2 := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_choose_two]
  push_cast at hbone henergy ⊢
  rw [hbone] at henergy
  nlinarith

theorem defects_d3k1
    (a k bones wrongPhaseStones threeOwnerBones : ℕ)
    (hbone : (bones : ℚ) = 3 * k * (a - 2 * k - 1))
    (henergy :
      (bones : ℚ) +
          3 * ((wrongPhaseStones : ℚ) + threeOwnerBones) =
        3 * k * (a - (3 * k + 1 : ℚ) / 2)) :
    wrongPhaseStones + threeOwnerBones = (k + 1).choose 2 := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_choose_two]
  push_cast at hbone henergy ⊢
  rw [hbone] at henergy
  nlinarith

end FiniteDefects
