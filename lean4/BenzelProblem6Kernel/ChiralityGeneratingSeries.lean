import BenzelProblem6Kernel.PathModelCarrier
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Positive- and negative-chirality generating series
-/

namespace BenzelProblem6Kernel

open scoped BigOperators
open PowerSeries

noncomputable def positiveLevelCount (degree : ℕ) : ℕ :=
  ∑ sink : SimplexPoint degree,
    positiveChiralityCount sink.u sink.v sink.w

noncomputable def negativeLevelCount (degree : ℕ) : ℕ :=
  ∑ sink : SimplexPoint degree,
    negativeChiralityCount sink.u sink.v sink.w

noncomputable def positiveChiralityGeneratingSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree => (positiveLevelCount degree : ℚ)

noncomputable def negativeChiralityGeneratingSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree => (negativeLevelCount degree : ℚ)

noncomputable def pathModelGeneratingSeries : ℚ⟦X⟧ :=
  positiveChiralityGeneratingSeries + negativeChiralityGeneratingSeries

@[simp] theorem coeff_positiveChiralityGeneratingSeries (degree : ℕ) :
    coeff ℚ degree positiveChiralityGeneratingSeries =
      (positiveLevelCount degree : ℚ) := by
  simp [positiveChiralityGeneratingSeries]

@[simp] theorem coeff_negativeChiralityGeneratingSeries (degree : ℕ) :
    coeff ℚ degree negativeChiralityGeneratingSeries =
      (negativeLevelCount degree : ℚ) := by
  simp [negativeChiralityGeneratingSeries]

theorem positive_add_negative_level_eq_pathModelCount (degree : ℕ) :
    positiveLevelCount degree + negativeLevelCount degree =
      pathModelCount degree := by
  simp only [positiveLevelCount, negativeLevelCount, pathModelCount,
    ← Finset.sum_add_distrib, fixedSinkCount]

theorem coeff_pathModelGeneratingSeries (degree : ℕ) :
    coeff ℚ degree pathModelGeneratingSeries =
      (pathModelCount degree : ℚ) := by
  rw [pathModelGeneratingSeries, map_add,
    coeff_positiveChiralityGeneratingSeries,
    coeff_negativeChiralityGeneratingSeries]
  exact_mod_cast positive_add_negative_level_eq_pathModelCount degree

end BenzelProblem6Kernel
