import BenzelProblem6Kernel.ClosedFormRecurrence
import BenzelProblem6Kernel.PathModelCarrier

/-!
# Uniqueness from the closed-form recurrence
-/

namespace BenzelProblem6Kernel

def recurrenceLeft (m : ℕ) : ℚ :=
  2 * (m + 1) * (m + 5) * (m + 6) * (2 * m + 11)

def recurrenceRight (m : ℕ) : ℚ :=
  3 * (m + 3) * (m + 7) * (3 * m + 10) * (3 * m + 11)

theorem recurrenceLeft_ne_zero (m : ℕ) : recurrenceLeft m ≠ 0 := by
  unfold recurrenceLeft
  positivity

theorem closedFormCount_recurrence_named (m : ℕ) :
    recurrenceLeft m * closedFormCount (m + 1) =
      recurrenceRight m * closedFormCount m := by
  exact closedFormCount_recurrence m

theorem sequence_eq_closedForm_of_recurrence
    (sequence : ℕ → ℚ)
    (hzero : sequence 0 = 2)
    (hrecurrence : ∀ m,
      recurrenceLeft m * sequence (m + 1) =
        recurrenceRight m * sequence m) :
    ∀ m, sequence m = closedFormCount m := by
  intro m
  induction m with
  | zero => rw [hzero, closedFormCount_zero]
  | succ m ih =>
      apply mul_left_cancel₀ (recurrenceLeft_ne_zero m)
      calc
        recurrenceLeft m * sequence (m + 1) =
            recurrenceRight m * sequence m := hrecurrence m
        _ = recurrenceRight m * closedFormCount m := by rw [ih]
        _ = recurrenceLeft m * closedFormCount (m + 1) :=
          (closedFormCount_recurrence_named m).symm

def pathModelRecurrenceTarget : Prop :=
  ∀ m,
    recurrenceLeft m * (pathModelCount (m + 1) : ℚ) =
      recurrenceRight m * (pathModelCount m : ℚ)

theorem pathModel_eq_closedForm_of_recurrence
    (hrecurrence : pathModelRecurrenceTarget) :
    ∀ m, (pathModelCount m : ℚ) = closedFormCount m := by
  apply sequence_eq_closedForm_of_recurrence
  · exact_mod_cast pathModelCount_zero
  · exact hrecurrence

end BenzelProblem6Kernel
