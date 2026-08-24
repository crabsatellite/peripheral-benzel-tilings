import BenzelProblem6Kernel.ChiralityCounts
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Final binomial simplification
-/

namespace BenzelProblem6Kernel

def choosePred (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => n.choose k

theorem ballot_form_eq_closed_form (m : ℕ) :
    (2 * ((3 * m + 8).choose m : ℚ) - choosePred (3 * m + 8) m) =
      (3 * (m + 6) : ℚ) / (2 * m + 9) * (3 * m + 8).choose m := by
  cases m with
  | zero => norm_num [choosePred]
  | succ k =>
      simp only [choosePred]
      have hkN : k ≤ 3 * (k + 1) + 8 := by omega
      have hskN : k + 1 ≤ 3 * (k + 1) + 8 := by omega
      have hsubk : 3 * (k + 1) + 8 - k = 2 * k + 11 := by omega
      have hsubsk : 3 * (k + 1) + 8 - (k + 1) = 2 * k + 10 := by omega
      rw [Nat.cast_choose ℚ hskN, Nat.cast_choose ℚ hkN]
      rw [hsubsk, hsubk]
      have hkfact : (Nat.factorial (k + 1) : ℚ) =
          ((k + 1 : ℕ) : ℚ) * (Nat.factorial k : ℚ) := by
        rw [Nat.factorial_succ]
        norm_cast
      have htail : 2 * k + 11 = (2 * k + 10) + 1 := by omega
      have htailfact : (Nat.factorial (2 * k + 11) : ℚ) =
          ((2 * k + 11 : ℕ) : ℚ) * (Nat.factorial (2 * k + 10) : ℚ) := by
        rw [htail, Nat.factorial_succ]
        norm_cast
      rw [hkfact, htailfact]
      push_cast
      field_simp
      ring

end BenzelProblem6Kernel
