import D4KernelOnly.D4BoundarySideFiveOccurrences

/-! # Reverse side-five occurrences in the physical d=4 boundary walk -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

def isReverseSideFiveEdge (edge : LabeledHexEdge) : Bool :=
  edge.label == .c && edge.target == addHexStep edge.source shadowC

def reverseSideFiveEdges (edges : List LabeledHexEdge) :
    List LabeledHexEdge := edges.filter isReverseSideFiveEdge

theorem reverseSideFiveEdges_append
    (left right : List LabeledHexEdge) :
    reverseSideFiveEdges (left ++ right) =
      reverseSideFiveEdges left ++ reverseSideFiveEdges right := by
  simp [reverseSideFiveEdges, List.filter_append]

theorem d4LiteralBlock5_reverse (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock5) =
      [advanceLabeledHexEdge source shadowC .c,
        advanceLabeledHexEdge
          (source.1 - 2, source.2 - 1) shadowC .c] := by
  rcases source with ⟨x, y⟩
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    d4LiteralStepBlock5, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock4_reverse (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock4) =
      [advanceLabeledHexEdge
        (source.1 + 1, source.2 - 2) shadowC .c] := by
  rcases source with ⟨x, y⟩
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    d4LiteralStepBlock4, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock3_reverse (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock3) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    d4LiteralStepBlock3, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock2_reverse (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock2) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    d4LiteralStepBlock2, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4LiteralBlock1_reverse (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock1) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    d4LiteralStepBlock1, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]

theorem d4LiteralBlock0_reverse (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source d4LiteralStepBlock0) =
      [advanceLabeledHexEdge
        (source.1 - 1, source.2) shadowC .c] := by
  rcases source with ⟨x, y⟩
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    d4LiteralStepBlock0, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
    ShadowStep.neg]
  all_goals omega

theorem d4Reverse_single_C (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source [(shadowC, .c)]) =
      [advanceLabeledHexEdge source shadowC .c] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4Reverse_single_negC (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source [(shadowC.neg, .c)]) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowC, ShadowStep.neg]

theorem d4Reverse_single_A (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source [(shadowA, .a)]) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4Reverse_single_negA (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source [(shadowA.neg, .a)]) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4Reverse_single_B (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source [(shadowB, .b)]) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4Reverse_single_negB (source : HexVertex) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source [(shadowB.neg, .b)]) = [] := by
  simp [reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge]

theorem d4LiteralBlock5_reverse_power
    (source : HexVertex) (exponent : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock5 exponent)) =
      (List.range exponent).flatMap fun r =>
        [advanceLabeledHexEdge
          (source.1 - 3 * (r : ℤ), source.2 - 3 * (r : ℤ))
          shadowC .c,
        advanceLabeledHexEdge
          (source.1 - 3 * (r : ℤ) - 2,
            source.2 - 3 * (r : ℤ) - 1) shadowC .c] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      have hpow := d4LiteralBlock5_walkEnd_power source exponent
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, hpow,
        d4LiteralBlock5_reverse, List.range_succ,
        List.flatMap_append]
      simp [walkPowerStart]
      constructor <;> congr 2 <;> ring

theorem d4LiteralBlock3_reverse_power
    (source : HexVertex) (exponent : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock3 exponent)) = [] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, d4LiteralBlock3_reverse,
        List.nil_append]

theorem d4LiteralBlock1_reverse_power
    (source : HexVertex) (exponent : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source
        (labeledStepWordPower d4LiteralStepBlock1 exponent)) = [] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, d4LiteralBlock1_reverse,
        List.nil_append]

def d4WalkReverseSideFiveCells (m : ℕ) : List Cell :=
  ((List.range (m + 1)).flatMap fun r =>
    [(-((m : ℤ)) - 2 + (r : ℤ),
        (m : ℤ) + 1 - 2 * (r : ℤ)),
      (-((m : ℤ)) - 2 + (r : ℤ),
        (m : ℤ) - 2 * (r : ℤ))]) ++
  [(-1, -((m : ℤ)) - 1),
    (1, -((m : ℤ)) - 2),
    (-((m : ℤ)) - 2, (m : ℤ) + 2)]

def d4WalkReverseSideFiveEdges (m : ℕ) : List LabeledHexEdge :=
  (d4WalkReverseSideFiveCells m).map fun cell =>
    reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)

theorem reverse_cellBoundaryEdgeAt_sideFive_formula (cell : Cell) :
    reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅) =
      advanceLabeledHexEdge
        (cell.1 + 2 * cell.2, -cell.1 + cell.2)
        shadowC .c := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  rcases cell with ⟨i, j⟩
  simp [reverseLabeledHexEdge, advanceLabeledHexEdge,
    addHexStep, shadowC, ShadowStep.neg]
  constructor <;> ring

theorem d4Block5ReverseEdge0_eq (m : ℕ) (r : ℤ) :
    advanceLabeledHexEdge
        ((d4Stage0 m).1 - 3 * r, (d4Stage0 m).2 - 3 * r)
        shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt
          (-((m : ℤ)) - 2 + r, (m : ℤ) + 1 - 2 * r) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage0] <;> ring
  · apply Prod.ext <;> simp [d4Stage0, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem d4Block5ReverseEdge1_eq (m : ℕ) (r : ℤ) :
    advanceLabeledHexEdge
        ((d4Stage0 m).1 - 3 * r - 2,
          (d4Stage0 m).2 - 3 * r - 1) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt
          (-((m : ℤ)) - 2 + r, (m : ℤ) - 2 * r) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage0] <;> ring
  · apply Prod.ext <;> simp [d4Stage0, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem d4SeparatorReverseEdge_eq (m : ℕ) :
    advanceLabeledHexEdge (d4Stage1 m) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt (-1, -((m : ℤ)) - 1) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage1] <;> ring
  · apply Prod.ext <;> simp [d4Stage1, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem d4Block4ReverseEdge_eq (m : ℕ) :
    advanceLabeledHexEdge
        ((d4Stage2 m).1 + 1, (d4Stage2 m).2 - 2) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt (1, -((m : ℤ)) - 2) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage2] <;> ring
  · apply Prod.ext <;> simp [d4Stage2, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem d4Block0ReverseEdge_eq (m : ℕ) :
    advanceLabeledHexEdge
        ((d4Stage10 m).1 - 1, (d4Stage10 m).2) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt
          (-((m : ℤ)) - 2, (m : ℤ) + 2) .side₅) := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4Stage10] <;> ring
  · apply Prod.ext <;> simp [d4Stage10, advanceLabeledHexEdge,
      addHexStep, shadowC] <;> ring
  · rfl

theorem d4LiteralBoundaryWalk_reverse (m : ℕ) :
    reverseSideFiveEdges (d4LiteralBoundaryWalk m) =
      d4WalkReverseSideFiveEdges m := by
  rw [d4LiteralBoundaryWalk_eq_segments]
  unfold d4LiteralBoundaryWalkBySegments
  simp only [reverseSideFiveEdges_append,
    d4LiteralBlock5_reverse_power, d4LiteralBlock4_reverse,
    d4LiteralBlock3_reverse_power, d4LiteralBlock2_reverse,
    d4LiteralBlock1_reverse_power, d4LiteralBlock0_reverse,
    d4Reverse_single_C, d4Reverse_single_negC,
    d4Reverse_single_A, d4Reverse_single_negA,
    d4Reverse_single_B, d4Reverse_single_negB,
    List.nil_append, List.append_nil]
  simp [d4Block5ReverseEdge0_eq, d4Block5ReverseEdge1_eq,
    d4SeparatorReverseEdge_eq, d4Block4ReverseEdge_eq,
    d4Block0ReverseEdge_eq,
    d4WalkReverseSideFiveEdges, d4WalkReverseSideFiveCells,
    List.map_append, List.map_flatMap, Function.comp_def]

end FiniteDefects
