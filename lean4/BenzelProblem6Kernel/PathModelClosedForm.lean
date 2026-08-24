import BenzelProblem6Kernel.WZFiniteTelescoping

/-!
# Premise-free closed form for the complete path model
-/

namespace BenzelProblem6Kernel

theorem pathModelCount_eq_closedFormCount (m : ℕ) :
    (pathModelCount m : ℚ) = closedFormCount m :=
  pathModel_eq_closedForm_of_recurrence pathModelRecurrenceTarget_proved m

theorem pathModelClosedFormTarget_proved : pathModelClosedFormTarget := by
  intro m
  rw [pathModelCount_eq_closedFormCount]
  exact (ballot_form_eq_closed_form m).symm

theorem card_pathModelConfiguration_closed_form (m : ℕ) :
    (Fintype.card (PathModelConfiguration m) : ℚ) =
      2 * (3 * m + 8).choose m - choosePred (3 * m + 8) m := by
  rw [card_pathModelConfiguration]
  exact pathModelClosedFormTarget_proved m

end BenzelProblem6Kernel
