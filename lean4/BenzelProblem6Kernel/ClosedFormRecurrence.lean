import BenzelProblem6Kernel.FinalBinomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Hypergeometric recurrence of the manuscript closed form
-/

namespace BenzelProblem6Kernel

def closedFormCount (m : ℕ) : ℚ :=
  (3 * (m + 6) : ℚ) / (2 * m + 9) * (3 * m + 8).choose m

theorem adjacent_ternary_choose_relation (m : ℕ) :
    ((3 * m + 11).choose (m + 1) : ℚ) * (m + 1) *
        (2 * m + 10) * (2 * m + 9) =
      ((3 * m + 8).choose m : ℚ) * (3 * m + 9) *
        (3 * m + 10) * (3 * m + 11) := by
  have h1 : ((3 * m + 8).choose m : ℚ) * (3 * m + 9) =
      ((3 * m + 9).choose m : ℚ) * (2 * m + 9) := by
    have h := Nat.choose_mul_succ_eq (3 * m + 8) m
    rw [show 3 * m + 8 + 1 = 3 * m + 9 by omega,
      show 3 * m + 8 + 1 - m = 2 * m + 9 by omega] at h
    exact_mod_cast h
  have h2 : ((3 * m + 9).choose m : ℚ) * (3 * m + 10) =
      ((3 * m + 10).choose m : ℚ) * (2 * m + 10) := by
    have h := Nat.choose_mul_succ_eq (3 * m + 9) m
    rw [show 3 * m + 9 + 1 = 3 * m + 10 by omega,
      show 3 * m + 9 + 1 - m = 2 * m + 10 by omega] at h
    exact_mod_cast h
  have h3 : ((3 * m + 10).choose m : ℚ) * (3 * m + 11) =
      ((3 * m + 11).choose m : ℚ) * (2 * m + 11) := by
    have h := Nat.choose_mul_succ_eq (3 * m + 10) m
    rw [show 3 * m + 10 + 1 = 3 * m + 11 by omega,
      show 3 * m + 10 + 1 - m = 2 * m + 11 by omega] at h
    exact_mod_cast h
  have h4 : ((3 * m + 11).choose (m + 1) : ℚ) * (m + 1) =
      ((3 * m + 11).choose m : ℚ) * (2 * m + 11) := by
    have h := Nat.choose_succ_right_eq (3 * m + 11) m
    rw [show 3 * m + 11 - m = 2 * m + 11 by omega] at h
    exact_mod_cast h
  calc
    ((3 * m + 11).choose (m + 1) : ℚ) * (m + 1) *
        (2 * m + 10) * (2 * m + 9) =
      (((3 * m + 10).choose m : ℚ) * (3 * m + 11)) *
        (2 * m + 10) * (2 * m + 9) := by rw [h4, ← h3]
    _ = ((((3 * m + 9).choose m : ℚ) * (3 * m + 10)) *
        (3 * m + 11)) * (2 * m + 9) := by rw [h2]; ring
    _ = (((3 * m + 9).choose m : ℚ) * (2 * m + 9)) *
        (3 * m + 10) * (3 * m + 11) := by ring
    _ = ((3 * m + 8).choose m : ℚ) * (3 * m + 9) *
        (3 * m + 10) * (3 * m + 11) := by rw [← h1]

theorem closedFormCount_recurrence (m : ℕ) :
    (2 * (m + 1) * (m + 5) * (m + 6) * (2 * m + 11) : ℚ) *
        closedFormCount (m + 1) =
      (3 * (m + 3) * (m + 7) * (3 * m + 10) * (3 * m + 11) : ℚ) *
        closedFormCount m := by
  have hchoose := adjacent_ternary_choose_relation m
  simp only [closedFormCount]
  rw [show 3 * (m + 1) + 8 = 3 * m + 11 by omega]
  push_cast
  field_simp
  linear_combination 3 * (m + 6) * (m + 7) * (2 * m + 11) * hchoose

theorem closedFormCount_zero : closedFormCount 0 = 2 := by
  norm_num [closedFormCount]

end BenzelProblem6Kernel
