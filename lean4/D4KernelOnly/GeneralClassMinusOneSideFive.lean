import D4KernelOnly.GeneralClassMinusOneSegments
import D4KernelOnly.D4BoundaryReverseSideFiveOccurrences

/-! # Side-five occurrences for the general class-minus-one boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem generalLiteralBlock4_forward_power
    (source : HexVertex) (exponent : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock4 exponent)) = [] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, d4LiteralBlock4_forward,
        List.nil_append]

theorem generalLiteralBlock2_forward_power
    (source : HexVertex) (exponent : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock2 exponent)) =
      (List.range exponent).flatMap fun q =>
        [advanceLabeledHexEdge
          (source.1 + 3 * (q : ℤ), source.2 + 3 * (q : ℤ))
          shadowC.neg .c,
        advanceLabeledHexEdge
          (source.1 + 3 * (q : ℤ) + 1,
            source.2 + 3 * (q : ℤ) + 2) shadowC.neg .c] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      have hpow := generalLiteralBlock2_walkEnd_power source exponent
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, hpow,
        d4LiteralBlock2_forward, List.range_succ, List.flatMap_append]
      simp [walkPowerStart]
      constructor <;> congr 2 <;> ring

theorem generalLiteralBlock0_forward_power
    (source : HexVertex) (exponent : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock0 exponent)) = [] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, d4LiteralBlock0_forward,
        List.nil_append]

theorem generalLiteralBlock2_reverse_power
    (source : HexVertex) (exponent : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock2 exponent)) = [] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, d4LiteralBlock2_reverse,
        List.nil_append]

theorem generalLiteralBlock4_reverse_power
    (source : HexVertex) (exponent : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock4 exponent)) =
      (List.range exponent).map fun q : ℕ =>
        advanceLabeledHexEdge
          (source.1 + 1, source.2 - 3 * (q : ℤ) - 2) shadowC .c := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      have hpow := generalLiteralBlock4_walkEnd_power source exponent
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, hpow,
        d4LiteralBlock4_reverse, List.range_succ, List.map_append]
      simp [walkPowerStart]
      congr 1
      apply Prod.ext <;> simp <;> ring

theorem generalLiteralBlock0_reverse_power
    (source : HexVertex) (exponent : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock0 exponent)) =
      (List.range exponent).map fun q : ℕ =>
        advanceLabeledHexEdge
          (source.1 - 3 * (q : ℤ) - 1, source.2) shadowC .c := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      have hpow := generalLiteralBlock0_walkEnd_power source exponent
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, hpow,
        d4LiteralBlock0_reverse, List.range_succ, List.map_append]
      simp [walkPowerStart]
      congr 1
      apply Prod.ext <;> simp <;> ring

def cmoWalkForwardSideFiveCells (s r : ℕ) : List Cell :=
  [((s : ℤ), -((r : ℤ)) - s)] ++
  (List.range r).map (fun q : ℕ =>
    ((s : ℤ) + q + 1, (q : ℤ) - r - s + 1)) ++
  (List.range s).flatMap (fun q : ℕ =>
    [((r : ℤ) + s - q, 2 * (q : ℤ) - s + 1),
      ((r : ℤ) + s - q - 1, 2 * (q : ℤ) - s + 2)]) ++
  (List.range r).map (fun q : ℕ =>
    ((r : ℤ) - 2 * q - 1, (s : ℤ) + q + 1))

def cmoWalkReverseSideFiveCells (s r : ℕ) : List Cell :=
  ((List.range r).flatMap fun q : ℕ =>
    [(-((r : ℤ)) - s + q, (r : ℤ) - 2 * q),
      (-((r : ℤ)) - s + q, (r : ℤ) - 2 * q - 1)]) ++
  [(-((s : ℤ)), -((r : ℤ)))] ++
  (List.range s).map (fun q : ℕ =>
    (-((s : ℤ)) + 2 + 2 * q, -((r : ℤ)) - 1 - q)) ++
  (List.range s).map (fun q : ℕ =>
    (-((r : ℤ)) - q - 1, (r : ℤ) + s - q))

def cmoWalkForwardSideFiveEdges (s r : ℕ) : List LabeledHexEdge :=
  (cmoWalkForwardSideFiveCells s r).map fun cell =>
    cellBoundaryEdgeAt cell .side₅

def cmoWalkReverseSideFiveEdges (s r : ℕ) : List LabeledHexEdge :=
  (cmoWalkReverseSideFiveCells s r).map fun cell =>
    reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)

theorem cmoSpurForwardEdge_eq (s r : ℕ) :
    advanceLabeledHexEdge (cmoStage3 s r) shadowC.neg .c =
      cellBoundaryEdgeAt (s, -((r : ℤ)) - s) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage3] <;> ring
  · apply Prod.ext <;> simp [cmoStage3, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem cmoBlock3ForwardEdge_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage4 s r).1 + 3 * q + 2,
          (cmoStage4 s r).2 - 1) shadowC.neg .c =
      cellBoundaryEdgeAt (s + q + 1, q - r - s + 1) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage4] <;> ring
  · apply Prod.ext <;> simp [cmoStage4, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem cmoBlock2ForwardEdge0_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage6 s r).1 + 3 * q,
          (cmoStage6 s r).2 + 3 * q) shadowC.neg .c =
      cellBoundaryEdgeAt (r + s - q, 2 * q - s + 1) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage6] <;> ring
  · apply Prod.ext <;> simp [cmoStage6, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem cmoBlock2ForwardEdge1_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage6 s r).1 + 3 * q + 1,
          (cmoStage6 s r).2 + 3 * q + 2) shadowC.neg .c =
      cellBoundaryEdgeAt (r + s - q - 1, 2 * q - s + 2) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage6] <;> ring
  · apply Prod.ext <;> simp [cmoStage6, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem cmoBlock1ForwardEdge_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage8 s r).1,
          (cmoStage8 s r).2 + 3 * q + 1) shadowC.neg .c =
      cellBoundaryEdgeAt (r - 2 * q - 1, s + q + 1) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage8] <;> ring
  · apply Prod.ext <;> simp [cmoStage8, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem cmoBlock5ReverseEdge0_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage0 s r).1 - 3 * q,
          (cmoStage0 s r).2 - 3 * q) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt (-r - s + q, r - 2 * q) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage0] <;> ring
  · apply Prod.ext <;> simp [cmoStage0, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem cmoBlock5ReverseEdge1_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage0 s r).1 - 3 * q - 2,
          (cmoStage0 s r).2 - 3 * q - 1) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt (-r - s + q, r - 2 * q - 1) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage0] <;> ring
  · apply Prod.ext <;> simp [cmoStage0, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem cmoSeparatorReverseEdge_eq (s r : ℕ) :
    advanceLabeledHexEdge (cmoStage1 s r) shadowC .c =
      reverseLabeledHexEdge (cellBoundaryEdgeAt (-s, -r) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage1] <;> ring
  · apply Prod.ext <;> simp [cmoStage1, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem cmoBlock4ReverseEdge_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage2 s r).1 + 1,
          (cmoStage2 s r).2 - 3 * q - 2) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt (-s + 2 + 2 * q, -r - 1 - q) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage2] <;> ring
  · apply Prod.ext <;> simp [cmoStage2, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem cmoBlock0ReverseEdge_eq (s r : ℕ) (q : ℤ) :
    advanceLabeledHexEdge
        ((cmoStage10 s r).1 - 3 * q - 1,
          (cmoStage10 s r).2) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt (-r - q - 1, r + s - q) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [cmoStage10] <;> ring
  · apply Prod.ext <;> simp [cmoStage10, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem classMinusOneBoundaryWalk_forward (s r : ℕ) :
    forwardSideFiveEdges (classMinusOneLiteralBoundaryWalk s r) =
      cmoWalkForwardSideFiveEdges s r := by
  rw [classMinusOneLiteralBoundaryWalk_eq_segments]
  unfold classMinusOneBoundaryWalkBySegments
  simp only [forwardSideFiveEdges_append,
    d4LiteralBlock5_forward_power, generalLiteralBlock4_forward_power,
    d4LiteralBlock3_forward_power, generalLiteralBlock2_forward_power,
    d4LiteralBlock1_forward_power, generalLiteralBlock0_forward_power,
    d4Forward_single_C, d4Forward_single_negC,
    d4Forward_single_A, d4Forward_single_negA,
    d4Forward_single_B, d4Forward_single_negB,
    List.nil_append, List.append_nil]
  simp [cmoSpurForwardEdge_eq, cmoBlock3ForwardEdge_eq,
    cmoBlock2ForwardEdge0_eq, cmoBlock2ForwardEdge1_eq,
    cmoBlock1ForwardEdge_eq,
    cmoWalkForwardSideFiveEdges, cmoWalkForwardSideFiveCells,
    List.map_append, List.map_flatMap, Function.comp_def]
  simp only [← List.map_eq_flatMap]

theorem classMinusOneBoundaryWalk_reverse (s r : ℕ) :
    reverseSideFiveEdges (classMinusOneLiteralBoundaryWalk s r) =
      cmoWalkReverseSideFiveEdges s r := by
  rw [classMinusOneLiteralBoundaryWalk_eq_segments]
  unfold classMinusOneBoundaryWalkBySegments
  simp only [reverseSideFiveEdges_append,
    d4LiteralBlock5_reverse_power, generalLiteralBlock4_reverse_power,
    d4LiteralBlock3_reverse_power, generalLiteralBlock2_reverse_power,
    d4LiteralBlock1_reverse_power, generalLiteralBlock0_reverse_power,
    d4Reverse_single_C, d4Reverse_single_negC,
    d4Reverse_single_A, d4Reverse_single_negA,
    d4Reverse_single_B, d4Reverse_single_negB,
    List.nil_append, List.append_nil]
  simp [cmoBlock5ReverseEdge0_eq, cmoBlock5ReverseEdge1_eq,
    cmoSeparatorReverseEdge_eq, cmoBlock4ReverseEdge_eq,
    cmoBlock0ReverseEdge_eq,
    cmoWalkReverseSideFiveEdges, cmoWalkReverseSideFiveCells,
    List.map_append, List.map_flatMap, Function.comp_def]

end FiniteDefects
