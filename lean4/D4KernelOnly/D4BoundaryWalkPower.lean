import D4KernelOnly.D4LiteralBoundaryBlocks

/-! # Cached append and power laws for physical labeled walks -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem labeledHexWalkEnd_append (source : HexVertex)
    (left right : List D4LabeledStep) :
    labeledHexWalkEnd source (left ++ right) =
      labeledHexWalkEnd (labeledHexWalkEnd source left) right := by
  induction left generalizing source with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, labeledHexWalkEnd]
      exact ih (addHexStep source head.1)

theorem walkLabeledHexEdges_append (source : HexVertex)
    (left right : List D4LabeledStep) :
    walkLabeledHexEdges source (left ++ right) =
      walkLabeledHexEdges source left ++
        walkLabeledHexEdges (labeledHexWalkEnd source left) right := by
  induction left generalizing source with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, walkLabeledHexEdges, List.cons_append,
        List.cons.injEq, true_and]
      exact ih (addHexStep source head.1)

def walkPowerStart (source displacement : HexVertex) (r : ℕ) : HexVertex :=
  (source.1 + (r : ℤ) * displacement.1,
    source.2 + (r : ℤ) * displacement.2)

theorem walkPowerStart_zero (source displacement : HexVertex) :
    walkPowerStart source displacement 0 = source := by
  apply Prod.ext <;> simp [walkPowerStart]

theorem walkPowerStart_succ (source displacement : HexVertex) (r : ℕ) :
    walkPowerStart source displacement (r + 1) =
      ((walkPowerStart source displacement r).1 + displacement.1,
        (walkPowerStart source displacement r).2 + displacement.2) := by
  apply Prod.ext <;> simp [walkPowerStart] <;> ring

theorem labeledHexWalkEnd_power
    (word : List D4LabeledStep) (displacement source : HexVertex)
    (hend : ∀ start, labeledHexWalkEnd start word =
      (start.1 + displacement.1, start.2 + displacement.2))
    (exponent : ℕ) :
    labeledHexWalkEnd source (labeledStepWordPower word exponent) =
      walkPowerStart source displacement exponent := by
  induction exponent with
  | zero => exact walkPowerStart_zero source displacement |>.symm
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, labeledHexWalkEnd_append, ih,
        hend, walkPowerStart_succ]

theorem walkLabeledHexEdges_power
    (word : List D4LabeledStep) (displacement source : HexVertex)
    (hend : ∀ start, labeledHexWalkEnd start word =
      (start.1 + displacement.1, start.2 + displacement.2))
    (exponent : ℕ) :
    walkLabeledHexEdges source (labeledStepWordPower word exponent) =
      (List.range exponent).flatMap fun r =>
        walkLabeledHexEdges (walkPowerStart source displacement r) word := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append, ih,
        labeledHexWalkEnd_power word displacement source hend exponent,
        List.range_succ, List.flatMap_append]
      simp [walkPowerStart]

end FiniteDefects
