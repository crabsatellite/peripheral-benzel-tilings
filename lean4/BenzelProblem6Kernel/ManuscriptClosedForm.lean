import BenzelProblem6Kernel.PathModelClosedForm
import BenzelProblem6Kernel.PathModelRationalKernel

/-!
# The manuscript factorial form of the path-model answer
-/

namespace BenzelProblem6Kernel

theorem pathModelCount_factorial_form (m : ℕ) :
    (pathModelCount m : ℚ) =
      ((3 * m + 18 : ℕ) : ℚ) * factorialQ (3 * m + 8) /
        (factorialQ m * factorialQ (2 * m + 9)) := by
  rw [pathModelCount_eq_closedFormCount]
  have hchoose := choose_cast_eq_factorial_ratio (3 * m + 8) m (by omega)
  rw [show 3 * m + 8 - m = 2 * m + 8 by omega] at hchoose
  have hfac := factorialQ_succ (2 * m + 8)
  rw [show 2 * m + 8 + 1 = 2 * m + 9 by omega] at hfac
  simp only [closedFormCount]
  rw [hchoose, hfac]
  field_simp [factorialQ_ne_zero]
  ring

theorem pathModelCount_manuscript_form {n : ℕ} (hn : 5 ≤ n) :
    (pathModelCount (n - 5) : ℚ) =
      ((3 * n + 3 : ℕ) : ℚ) * factorialQ (3 * n - 7) /
        (factorialQ (n - 5) * factorialQ (2 * n - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h0 : 5 + m - 5 = m := by omega
  have h1 : 3 * (5 + m) + 3 = 3 * m + 18 := by omega
  have h2 : 3 * (5 + m) - 7 = 3 * m + 8 := by omega
  have h3 : 2 * (5 + m) - 1 = 2 * m + 9 := by omega
  rw [h0, h1, h2, h3]
  exact pathModelCount_factorial_form m

theorem card_pathModelConfiguration_manuscript_form {n : ℕ} (hn : 5 ≤ n) :
    (Fintype.card (PathModelConfiguration (n - 5)) : ℚ) =
      ((3 * n + 3 : ℕ) : ℚ) * factorialQ (3 * n - 7) /
        (factorialQ (n - 5) * factorialQ (2 * n - 1)) := by
  rw [card_pathModelConfiguration]
  exact pathModelCount_manuscript_form hn

end BenzelProblem6Kernel
