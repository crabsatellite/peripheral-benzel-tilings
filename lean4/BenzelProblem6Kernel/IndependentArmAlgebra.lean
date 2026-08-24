import BenzelProblem6Kernel.ChiralityCounts
import Mathlib.Tactic.Ring

/-!
# Fixed-sink independent-arm algebra
-/

namespace BenzelProblem6Kernel

def positiveArmCount (minority adjacent : ℕ) : ℕ :=
  (2 * minority + adjacent + 2).choose (minority + 1) -
    (2 * minority + adjacent + 2).choose minority

def positiveArmTripleCount (x y z : ℕ) : ℕ :=
  positiveArmCount z x * positiveArmCount x y * positiveArmCount y z

theorem choose_le_choose_succ_for_arm (minority adjacent : ℕ) :
    (2 * minority + adjacent + 2).choose minority ≤
      (2 * minority + adjacent + 2).choose (minority + 1) := by
  let total := 2 * minority + adjacent + 2
  have hchoose := Nat.choose_succ_right_eq total minority
  have hsub : total - minority = minority + adjacent + 2 := by
    dsimp [total]
    omega
  rw [hsub] at hchoose
  apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < minority + 1)
  calc
    total.choose minority * (minority + 1) ≤
        total.choose minority * (minority + adjacent + 2) := by
      exact Nat.mul_le_mul_left _ (by omega)
    _ = total.choose (minority + 1) * (minority + 1) := hchoose.symm

theorem positiveArmCount_mul (minority adjacent : ℕ) :
    positiveArmCount minority adjacent * (minority + 1) =
      (adjacent + 1) *
        (2 * minority + adjacent + 2).choose minority := by
  let total := 2 * minority + adjacent + 2
  have hchoose := Nat.choose_succ_right_eq total minority
  have hsub : total - minority = minority + adjacent + 2 := by
    dsimp [total]
    omega
  rw [hsub] at hchoose
  simp only [positiveArmCount]
  rw [Nat.sub_mul]
  rw [hchoose]
  rw [← Nat.mul_sub_left_distrib]
  have hgap : minority + adjacent + 2 - (minority + 1) = adjacent + 1 := by
    omega
  rw [hgap]
  simp [total, Nat.mul_comm]

theorem positiveArmTripleCount_eq (x y z : ℕ) :
    positiveArmTripleCount x y z = positiveChiralityCount x y z := by
  have hxy := positiveArmCount_mul x y
  have hyz := positiveArmCount_mul y z
  have hzx := positiveArmCount_mul z x
  let cancelFactor := (x + 1) * (y + 1) * (z + 1)
  have hcancel : 0 < cancelFactor := by
    dsimp [cancelFactor]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  apply Nat.mul_right_cancel hcancel
  calc
    positiveArmTripleCount x y z * cancelFactor =
        (positiveArmCount z x * (z + 1)) *
        (positiveArmCount x y * (x + 1)) *
        (positiveArmCount y z * (y + 1)) := by
      simp [positiveArmTripleCount, cancelFactor]
      ring
    _ = ((x + 1) * (2 * z + x + 2).choose z) *
        ((y + 1) * (2 * x + y + 2).choose x) *
        ((z + 1) * (2 * y + z + 2).choose y) := by
      rw [hzx, hxy, hyz]
    _ = positiveChiralityCount x y z * cancelFactor := by
      simp [positiveChiralityCount, cancelFactor]
      ring

end BenzelProblem6Kernel
