import D4KernelOnly.D4BoundaryWalkPower
import D4KernelOnly.D4SideFiveCells

/-! # Side-five edge occurrences in the explicit physical boundary walk -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def isForwardSideFiveEdge (edge : LabeledHexEdge) : Bool :=
  edge.label == .c &&
    edge.target == addHexStep edge.source shadowC.neg

def forwardSideFiveEdges (edges : List LabeledHexEdge) :
    List LabeledHexEdge :=
  edges.filter isForwardSideFiveEdge

theorem forwardSideFiveEdges_append
    (left right : List LabeledHexEdge) :
    forwardSideFiveEdges (left ++ right) =
      forwardSideFiveEdges left ++ forwardSideFiveEdges right := by
  simp [forwardSideFiveEdges, List.filter_append]

theorem forwardSideFive_walk_append (source : HexVertex)
    (left right : List D4LabeledStep) :
    forwardSideFiveEdges (walkLabeledHexEdges source (left ++ right)) =
      forwardSideFiveEdges (walkLabeledHexEdges source left) ++
        forwardSideFiveEdges
          (walkLabeledHexEdges (labeledHexWalkEnd source left) right) := by
  rw [walkLabeledHexEdges_append, forwardSideFiveEdges_append]

theorem d4LiteralBlock5_forward (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock5) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    d4LiteralStepBlock5, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock4_forward (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock4) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    d4LiteralStepBlock4, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock3_forward (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock3) =
      [advanceLabeledHexEdge
        (source.1 + 2, source.2 - 1) shadowC.neg .c] := by
  rcases source with ⟨x, y⟩
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    d4LiteralStepBlock3, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock2_forward (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock2) =
      [advanceLabeledHexEdge source shadowC.neg .c,
        advanceLabeledHexEdge
          (source.1 + 1, source.2 + 2) shadowC.neg .c] := by
  rcases source with ⟨x, y⟩
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    d4LiteralStepBlock2, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock1_forward (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock1) =
      [advanceLabeledHexEdge
        (source.1, source.2 + 1) shadowC.neg .c] := by
  rcases source with ⟨x, y⟩
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    d4LiteralStepBlock1, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]

theorem d4LiteralBlock0_forward (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock0) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    d4LiteralStepBlock0, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]

theorem d4Forward_single_C (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source [(shadowC, .c)]) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowC, ShadowStep.neg]

theorem d4Forward_single_negC (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source [(shadowC.neg, .c)]) =
      [advanceLabeledHexEdge source shadowC.neg .c] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowC, ShadowStep.neg]

theorem d4Forward_single_A (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source [(shadowA, .a)]) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4Forward_single_negA (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source [(shadowA.neg, .a)]) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4Forward_single_B (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source [(shadowB, .b)]) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4Forward_single_negB (source : HexVertex) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source [(shadowB.neg, .b)]) = [] := by
  simp [forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

def d4WalkForwardSideFiveCells (m : ℕ) : List Cell :=
  [(1, -((m : ℤ)) - 2)] ++
  (List.range (m + 1)).map (fun r =>
    ((r : ℤ) + 2, (r : ℤ) - (m : ℤ) - 1)) ++
  [((m : ℤ) + 2, 0), ((m : ℤ) + 1, 1)] ++
  (List.range (m + 1)).map (fun r =>
    ((m : ℤ) - 2 * (r : ℤ), (r : ℤ) + 2))

def d4WalkForwardSideFiveEdges (m : ℕ) : List LabeledHexEdge :=
  (d4WalkForwardSideFiveCells m).map fun cell =>
    cellBoundaryEdgeAt cell .side₅

theorem cellBoundaryEdgeAt_sideFive_formula (cell : Cell) :
    cellBoundaryEdgeAt cell .side₅ =
      advanceLabeledHexEdge
        (cell.1 + 2 * cell.2 - 1, -cell.1 + cell.2 - 1)
        shadowC.neg .c := by
  rcases cell with ⟨i, j⟩
  simp [cellBoundaryEdgeAt, hexCellStartVertex, hexCellCenter,
    addHexStep, shadowA, shadowB, shadowC, ShadowStep.neg,
    advanceLabeledHexEdge]
  all_goals omega

theorem d4LiteralBlock3_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source d4LiteralStepBlock3 =
      (source.1 + 3, source.2) := by
  rcases source with ⟨x, y⟩
  simp [d4LiteralStepBlock3, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock1_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source d4LiteralStepBlock1 =
      (source.1, source.2 + 3) := by
  rcases source with ⟨x, y⟩
  simp [d4LiteralStepBlock1, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock5_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source d4LiteralStepBlock5 =
      (source.1 - 3, source.2 - 3) := by
  rcases source with ⟨x, y⟩
  simp [d4LiteralStepBlock5, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock4_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source d4LiteralStepBlock4 =
      (source.1, source.2 - 3) := by
  rcases source with ⟨x, y⟩
  simp [d4LiteralStepBlock4, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock2_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source d4LiteralStepBlock2 =
      (source.1 + 3, source.2 + 3) := by
  rcases source with ⟨x, y⟩
  simp [d4LiteralStepBlock2, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock0_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source d4LiteralStepBlock0 =
      (source.1 - 3, source.2) := by
  rcases source with ⟨x, y⟩
  simp [d4LiteralStepBlock0, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock3_forward_power
    (source : HexVertex) (exponent : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock3 exponent)) =
      (List.range exponent).map fun r =>
        advanceLabeledHexEdge
          (source.1 + 3 * (r : ℤ) + 2, source.2 - 1)
          shadowC.neg .c := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      have hpow := labeledHexWalkEnd_power d4LiteralStepBlock3
        (3, 0) source (fun start => by
          simpa using d4LiteralBlock3_walkEnd start) exponent
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, hpow,
        d4LiteralBlock3_forward]
      simp [List.range_succ, List.map_append, walkPowerStart]
      congr 2
      ring

theorem d4LiteralBlock1_forward_power
    (source : HexVertex) (exponent : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock1 exponent)) =
      (List.range exponent).map fun r =>
        advanceLabeledHexEdge
          (source.1, source.2 + 3 * (r : ℤ) + 1)
          shadowC.neg .c := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      have hpow := labeledHexWalkEnd_power d4LiteralStepBlock1
        (0, 3) source (fun start => by
          simpa using d4LiteralBlock1_walkEnd start) exponent
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, hpow,
        d4LiteralBlock1_forward]
      simp [List.range_succ, List.map_append, walkPowerStart]
      congr 2
      ring

theorem d4LiteralBlock5_forward_power
    (source : HexVertex) (exponent : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock5 exponent)) = [] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, d4LiteralBlock5_forward,
        List.nil_append]

theorem d4LiteralBlock5_walkEnd_power
    (source : HexVertex) (exponent : ℕ) :
    labeledHexWalkEnd source
        (labeledStepWordPower d4LiteralStepBlock5 exponent) =
      walkPowerStart source (-3, -3) exponent := by
  exact labeledHexWalkEnd_power d4LiteralStepBlock5 (-3, -3) source
    (fun start => by simpa using d4LiteralBlock5_walkEnd start) exponent

theorem d4LiteralBlock3_walkEnd_power
    (source : HexVertex) (exponent : ℕ) :
    labeledHexWalkEnd source
        (labeledStepWordPower d4LiteralStepBlock3 exponent) =
      walkPowerStart source (3, 0) exponent := by
  exact labeledHexWalkEnd_power d4LiteralStepBlock3 (3, 0) source
    (fun start => by simpa using d4LiteralBlock3_walkEnd start) exponent

theorem d4LiteralBlock1_walkEnd_power
    (source : HexVertex) (exponent : ℕ) :
    labeledHexWalkEnd source
        (labeledStepWordPower d4LiteralStepBlock1 exponent) =
      walkPowerStart source (0, 3) exponent := by
  exact labeledHexWalkEnd_power d4LiteralStepBlock1 (0, 3) source
    (fun start => by simpa using d4LiteralBlock1_walkEnd start) exponent

def d4Stage0 (m : ℕ) : HexVertex := ((m : ℤ), 2 * (m : ℤ) + 3)
def d4Stage1 (m : ℕ) : HexVertex := (-2 * (m : ℤ) - 3, -((m : ℤ)))
def d4Stage2 (m : ℕ) : HexVertex := (-2 * (m : ℤ) - 4, -((m : ℤ)) - 1)
def d4Stage3 (m : ℕ) : HexVertex := (-2 * (m : ℤ) - 4, -((m : ℤ)) - 4)
def d4Stage4 (m : ℕ) : HexVertex := (-2 * (m : ℤ) - 3, -((m : ℤ)) - 3)
def d4Stage5 (m : ℕ) : HexVertex := ((m : ℤ), -((m : ℤ)) - 3)
def d4Stage6 (m : ℕ) : HexVertex := ((m : ℤ) + 1, -((m : ℤ)) - 3)
def d4Stage7 (m : ℕ) : HexVertex := ((m : ℤ) + 4, -((m : ℤ)))
def d4Stage8 (m : ℕ) : HexVertex := ((m : ℤ) + 3, -((m : ℤ)))
def d4Stage9 (m : ℕ) : HexVertex := ((m : ℤ) + 3, 2 * (m : ℤ) + 3)
def d4Stage10 (m : ℕ) : HexVertex := ((m : ℤ) + 3, 2 * (m : ℤ) + 4)
def d4Stage11 (m : ℕ) : HexVertex := ((m : ℤ), 2 * (m : ℤ) + 4)

theorem d4Stage0_eq_root (m : ℕ) :
    d4Stage0 m = d4LiteralBoundaryRoot m := rfl

theorem d4Stage1_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage0 m)
      (labeledStepWordPower d4LiteralStepBlock5 (m + 1)) = d4Stage1 m := by
  rw [d4LiteralBlock5_walkEnd_power]
  apply Prod.ext <;> simp [d4Stage0, d4Stage1, walkPowerStart] <;> ring

theorem d4Stage2_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage1 m) [(shadowC, .c)] = d4Stage2 m := by
  apply Prod.ext <;> simp [d4Stage1, d4Stage2, labeledHexWalkEnd,
    addHexStep, shadowC] <;> ring

theorem d4Stage3_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage2 m) d4LiteralStepBlock4 = d4Stage3 m := by
  rw [d4LiteralBlock4_walkEnd]
  apply Prod.ext <;> simp [d4Stage2, d4Stage3] <;> ring

theorem d4Stage4_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage3 m) [(shadowC.neg, .c)] = d4Stage4 m := by
  apply Prod.ext <;> simp [d4Stage3, d4Stage4, labeledHexWalkEnd,
    addHexStep, shadowC, ShadowStep.neg] <;> ring

theorem d4Stage5_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage4 m)
      (labeledStepWordPower d4LiteralStepBlock3 (m + 1)) = d4Stage5 m := by
  rw [d4LiteralBlock3_walkEnd_power]
  apply Prod.ext <;> simp [d4Stage4, d4Stage5, walkPowerStart] <;> ring

theorem d4Stage6_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage5 m) [(shadowA, .a)] = d4Stage6 m := by
  apply Prod.ext <;> simp [d4Stage5, d4Stage6, labeledHexWalkEnd,
    addHexStep, shadowA] <;> ring

theorem d4Stage7_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage6 m) d4LiteralStepBlock2 = d4Stage7 m := by
  rw [d4LiteralBlock2_walkEnd]
  apply Prod.ext <;> simp [d4Stage6, d4Stage7] <;> ring

theorem d4Stage8_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage7 m) [(shadowA.neg, .a)] = d4Stage8 m := by
  apply Prod.ext <;> simp [d4Stage7, d4Stage8, labeledHexWalkEnd,
    addHexStep, shadowA, ShadowStep.neg] <;> ring

theorem d4Stage9_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage8 m)
      (labeledStepWordPower d4LiteralStepBlock1 (m + 1)) = d4Stage9 m := by
  rw [d4LiteralBlock1_walkEnd_power]
  apply Prod.ext <;> simp [d4Stage8, d4Stage9, walkPowerStart] <;> ring

theorem d4Stage10_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage9 m) [(shadowB, .b)] = d4Stage10 m := by
  apply Prod.ext <;> simp [d4Stage9, d4Stage10, labeledHexWalkEnd,
    addHexStep, shadowB] <;> ring

theorem d4Stage11_eq (m : ℕ) :
    labeledHexWalkEnd (d4Stage10 m) d4LiteralStepBlock0 = d4Stage11 m := by
  rw [d4LiteralBlock0_walkEnd]
  apply Prod.ext <;> simp [d4Stage10, d4Stage11] <;> ring

def d4LiteralBoundaryWalkBySegments (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4Stage0 m)
      (labeledStepWordPower d4LiteralStepBlock5 (m + 1)) ++
  (walkLabeledHexEdges (d4Stage1 m) [(shadowC, .c)] ++
  (walkLabeledHexEdges (d4Stage2 m) d4LiteralStepBlock4 ++
  (walkLabeledHexEdges (d4Stage3 m) [(shadowC.neg, .c)] ++
  (walkLabeledHexEdges (d4Stage4 m)
      (labeledStepWordPower d4LiteralStepBlock3 (m + 1)) ++
  (walkLabeledHexEdges (d4Stage5 m) [(shadowA, .a)] ++
  (walkLabeledHexEdges (d4Stage6 m) d4LiteralStepBlock2 ++
  (walkLabeledHexEdges (d4Stage7 m) [(shadowA.neg, .a)] ++
  (walkLabeledHexEdges (d4Stage8 m)
      (labeledStepWordPower d4LiteralStepBlock1 (m + 1)) ++
  (walkLabeledHexEdges (d4Stage9 m) [(shadowB, .b)] ++
  (walkLabeledHexEdges (d4Stage10 m) d4LiteralStepBlock0 ++
    walkLabeledHexEdges (d4Stage11 m) [(shadowB.neg, .b)]))))))))))

theorem d4LiteralBoundaryWalk_eq_segments (m : ℕ) :
    d4LiteralBoundaryWalk m = d4LiteralBoundaryWalkBySegments m := by
  rw [d4LiteralBoundaryWalk, d4LiteralBoundarySteps_eq_explicit]
  unfold d4LiteralBoundaryStepsExplicit
  rw [← d4Stage0_eq_root]
  rw [walkLabeledHexEdges_append, d4Stage1_eq]
  rw [walkLabeledHexEdges_append, d4Stage2_eq]
  rw [walkLabeledHexEdges_append, d4Stage3_eq]
  rw [walkLabeledHexEdges_append, d4Stage4_eq]
  rw [walkLabeledHexEdges_append, d4Stage5_eq]
  rw [walkLabeledHexEdges_append, d4Stage6_eq]
  rw [walkLabeledHexEdges_append, d4Stage7_eq]
  rw [walkLabeledHexEdges_append, d4Stage8_eq]
  rw [walkLabeledHexEdges_append, d4Stage9_eq]
  rw [walkLabeledHexEdges_append, d4Stage10_eq]
  rw [walkLabeledHexEdges_append, d4Stage11_eq]
  rfl

theorem d4SpurForwardEdge_eq (m : ℕ) :
    advanceLabeledHexEdge (d4Stage3 m) shadowC.neg .c =
      cellBoundaryEdgeAt (1, -((m : ℤ)) - 2) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage3] <;> ring
  · apply Prod.ext <;> simp [d4Stage3, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem d4Block3ForwardEdge_eq (m r : ℕ) :
    advanceLabeledHexEdge
        ((d4Stage4 m).1 + 3 * (r : ℤ) + 2,
          (d4Stage4 m).2 - 1) shadowC.neg .c =
      cellBoundaryEdgeAt
        ((r : ℤ) + 2, (r : ℤ) - (m : ℤ) - 1) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage4] <;> ring
  · apply Prod.ext <;> simp [d4Stage4, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem d4Block3ForwardEdgeZ_eq (m : ℕ) (r : ℤ) :
    advanceLabeledHexEdge
        ((d4Stage4 m).1 + 3 * r + 2, (d4Stage4 m).2 - 1)
        shadowC.neg .c =
      cellBoundaryEdgeAt
        (r + 2, r - (m : ℤ) - 1) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage4] <;> ring
  · apply Prod.ext <;> simp [d4Stage4, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem d4Block2ForwardEdge0_eq (m : ℕ) :
    advanceLabeledHexEdge (d4Stage6 m) shadowC.neg .c =
      cellBoundaryEdgeAt ((m : ℤ) + 2, 0) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage6] <;> ring
  · apply Prod.ext <;> simp [d4Stage6, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem d4Block2ForwardEdge1_eq (m : ℕ) :
    advanceLabeledHexEdge
        ((d4Stage6 m).1 + 1, (d4Stage6 m).2 + 2)
        shadowC.neg .c =
      cellBoundaryEdgeAt ((m : ℤ) + 1, 1) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage6] <;> ring
  · apply Prod.ext <;> simp [d4Stage6, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem d4Block1ForwardEdge_eq (m r : ℕ) :
    advanceLabeledHexEdge
        ((d4Stage8 m).1, (d4Stage8 m).2 + 3 * (r : ℤ) + 1)
        shadowC.neg .c =
      cellBoundaryEdgeAt
        ((m : ℤ) - 2 * (r : ℤ), (r : ℤ) + 2) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage8] <;> ring
  · apply Prod.ext <;> simp [d4Stage8, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem d4Block1ForwardEdgeZ_eq (m : ℕ) (r : ℤ) :
    advanceLabeledHexEdge
        ((d4Stage8 m).1, (d4Stage8 m).2 + 3 * r + 1)
        shadowC.neg .c =
      cellBoundaryEdgeAt
        ((m : ℤ) - 2 * r, r + 2) .side₅ := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage8] <;> ring
  · apply Prod.ext <;> simp [d4Stage8, advanceLabeledHexEdge,
      addHexStep, shadowC, ShadowStep.neg] <;> ring
  · rfl

theorem d4LiteralBoundaryWalk_forward (m : ℕ) :
    forwardSideFiveEdges (d4LiteralBoundaryWalk m) =
      d4WalkForwardSideFiveEdges m := by
  rw [d4LiteralBoundaryWalk_eq_segments]
  unfold d4LiteralBoundaryWalkBySegments
  simp only [forwardSideFiveEdges_append,
    d4LiteralBlock5_forward_power, d4LiteralBlock4_forward,
    d4LiteralBlock3_forward_power, d4LiteralBlock2_forward,
    d4LiteralBlock1_forward_power, d4LiteralBlock0_forward,
    d4Forward_single_C, d4Forward_single_negC,
    d4Forward_single_A, d4Forward_single_negA,
    d4Forward_single_B, d4Forward_single_negB,
    List.nil_append, List.append_nil]
  simp [d4SpurForwardEdge_eq, d4Block3ForwardEdge_eq,
    d4Block3ForwardEdgeZ_eq,
    d4Block2ForwardEdge0_eq, d4Block2ForwardEdge1_eq,
    d4Block1ForwardEdge_eq, d4Block1ForwardEdgeZ_eq,
    d4WalkForwardSideFiveEdges, d4WalkForwardSideFiveCells,
    List.map_append, Function.comp_def]

end FiniteDefects
