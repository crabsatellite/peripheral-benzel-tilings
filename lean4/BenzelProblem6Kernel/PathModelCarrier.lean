import BenzelProblem6Kernel.ArmCarriers
import BenzelProblem6Kernel.SimplexCardinality
import BenzelProblem6Kernel.FinalBinomial
import Mathlib.Data.Fintype.BigOperators

/-!
# The complete fixed-sink path-model carrier
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

abbrev FixedSinkArmChoice (x y z : ℕ) :=
  PositiveArmTriple x y z ⊕ NegativeArmTriple x y z

abbrev PathModelConfiguration (m : ℕ) :=
  Σ sink : SimplexPoint m, FixedSinkArmChoice sink.u sink.v sink.w

noncomputable def pathModelCount (m : ℕ) : ℕ :=
  ∑ sink : SimplexPoint m, fixedSinkCount sink.u sink.v sink.w

theorem card_fixedSinkArmChoice (x y z : ℕ) :
    Fintype.card (FixedSinkArmChoice x y z) = fixedSinkCount x y z := by
  rw [Fintype.card_sum, card_positiveArmTriple, card_negativeArmTriple]
  rfl

theorem card_pathModelConfiguration (m : ℕ) :
    Fintype.card (PathModelConfiguration m) = pathModelCount m := by
  rw [Fintype.card_sigma]
  simp_rw [card_fixedSinkArmChoice]
  rfl

theorem pathModelCount_zero : pathModelCount 0 = 2 := by
  classical
  have hsink (p : SimplexPoint 0) : p = sourceZero 0 := by
    apply simplexPoint_ext <;>
      simp [sourceZero] <;>
      have hsum := p.sum_eq <;>
      omega
  letI : Unique (SimplexPoint 0) := ⟨⟨sourceZero 0⟩, hsink⟩
  rw [pathModelCount, Fintype.sum_unique]
  have hdefault : (default : SimplexPoint 0) = sourceZero 0 := hsink _
  rw [hdefault]
  simp [sourceZero]

def pathModelClosedFormTarget : Prop :=
  ∀ m : ℕ,
    (pathModelCount m : ℚ) =
      2 * (3 * m + 8).choose m - choosePred (3 * m + 8) m

end BenzelProblem6Kernel
