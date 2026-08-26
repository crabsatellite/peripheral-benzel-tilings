import D4KernelOnly.GeneralClassZeroSegments
import D4KernelOnly.D4BoundaryReverseSideFiveOccurrences

/-! # Side-five occurrences in the general class-zero boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem czBlock5_forward (source : HexVertex) :
    forwardSideFiveEdges (walkLabeledHexEdges source czLiteralBlock5) =
      [advanceLabeledHexEdge (source.1 - 1, source.2 + 2) shadowC.neg .c] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock5, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₅, forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock4_forward (source : HexVertex) :
    forwardSideFiveEdges (walkLabeledHexEdges source czLiteralBlock4) = [] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock4, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₄, forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock3_forward (source : HexVertex) :
    forwardSideFiveEdges (walkLabeledHexEdges source czLiteralBlock3) = [] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock3, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₃, forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock2_forward (source : HexVertex) :
    forwardSideFiveEdges (walkLabeledHexEdges source czLiteralBlock2) = [] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock2, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₂, forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock1_forward (source : HexVertex) :
    forwardSideFiveEdges (walkLabeledHexEdges source czLiteralBlock1) =
      [advanceLabeledHexEdge (source.1 + 1, source.2) shadowC.neg .c] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock1, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₁, forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock0_forward (source : HexVertex) :
    forwardSideFiveEdges (walkLabeledHexEdges source czLiteralBlock0) =
      [advanceLabeledHexEdge (source.1, source.2 + 1) shadowC.neg .c,
        advanceLabeledHexEdge (source.1 + 2, source.2 + 2) shadowC.neg .c] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock0, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₀, forwardSideFiveEdges, isForwardSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock5_reverse (source : HexVertex) :
    reverseSideFiveEdges (walkLabeledHexEdges source czLiteralBlock5) = [] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock5, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₅, reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock4_reverse (source : HexVertex) :
    reverseSideFiveEdges (walkLabeledHexEdges source czLiteralBlock4) =
      [advanceLabeledHexEdge source shadowC .c] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock4, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₄, reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock3_reverse (source : HexVertex) :
    reverseSideFiveEdges (walkLabeledHexEdges source czLiteralBlock3) =
      [advanceLabeledHexEdge source shadowC .c,
        advanceLabeledHexEdge (source.1 - 1, source.2 - 2) shadowC .c] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock3, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₃, reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock2_reverse (source : HexVertex) :
    reverseSideFiveEdges (walkLabeledHexEdges source czLiteralBlock2) =
      [advanceLabeledHexEdge (source.1 + 1, source.2 - 1) shadowC .c] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock2, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₂, reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock1_reverse (source : HexVertex) :
    reverseSideFiveEdges (walkLabeledHexEdges source czLiteralBlock1) = [] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock1, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₁, reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock0_reverse (source : HexVertex) :
    reverseSideFiveEdges (walkLabeledHexEdges source czLiteralBlock0) = [] := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock0, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₀, reverseSideFiveEdges, isReverseSideFiveEdge,
    walkLabeledHexEdges, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czBlock5_forward_power (source : HexVertex) (n : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower czLiteralBlock5 n)) =
      (List.range n).map fun q : ℕ =>
        advanceLabeledHexEdge (source.1 - 1, source.2 + 3 * (q : ℤ) + 2)
          shadowC.neg .c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hend := czLiteralBlock5_walkEnd_power source n
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, hend, czBlock5_forward,
        List.range_succ, List.map_append]
      simp [walkPowerStart]
      congr 1
      apply Prod.ext <;> simp <;> ring

theorem czBlock1_forward_power (source : HexVertex) (n : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower czLiteralBlock1 n)) =
      (List.range n).map fun q : ℕ =>
        advanceLabeledHexEdge (source.1 + 3 * (q : ℤ) + 1, source.2)
          shadowC.neg .c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hend := czLiteralBlock1_walkEnd_power source n
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, hend, czBlock1_forward,
        List.range_succ, List.map_append]
      simp [walkPowerStart]
      congr 1
      apply Prod.ext <;> simp <;> ring

theorem czBlock0_forward_power (source : HexVertex) (n : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower czLiteralBlock0 n)) =
      (List.range n).flatMap fun q : ℕ =>
        [advanceLabeledHexEdge
          (source.1 + 3 * (q : ℤ), source.2 + 3 * (q : ℤ) + 1)
            shadowC.neg .c,
        advanceLabeledHexEdge
          (source.1 + 3 * (q : ℤ) + 2, source.2 + 3 * (q : ℤ) + 2)
            shadowC.neg .c] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hend := czLiteralBlock0_walkEnd_power source n
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, hend, czBlock0_forward,
        List.range_succ, List.flatMap_append]
      simp [walkPowerStart]
      constructor <;> congr 2 <;> ring

theorem czBlock4_reverse_power (source : HexVertex) (n : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower czLiteralBlock4 n)) =
      (List.range n).map fun q : ℕ =>
        advanceLabeledHexEdge (source.1 - 3 * (q : ℤ), source.2) shadowC .c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hend := czLiteralBlock4_walkEnd_power source n
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, hend, czBlock4_reverse,
        List.range_succ, List.map_append]
      simp [walkPowerStart]
      congr 1
      apply Prod.ext <;> simp <;> ring

theorem czBlock3_reverse_power (source : HexVertex) (n : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower czLiteralBlock3 n)) =
      (List.range n).flatMap fun q : ℕ =>
        [advanceLabeledHexEdge
          (source.1 - 3 * (q : ℤ), source.2 - 3 * (q : ℤ)) shadowC .c,
        advanceLabeledHexEdge
          (source.1 - 3 * (q : ℤ) - 1, source.2 - 3 * (q : ℤ) - 2)
            shadowC .c] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hend := czLiteralBlock3_walkEnd_power source n
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, hend, czBlock3_reverse,
        List.range_succ, List.flatMap_append]
      simp [walkPowerStart]
      constructor <;> congr 2 <;> ring

theorem czBlock2_reverse_power (source : HexVertex) (n : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower czLiteralBlock2 n)) =
      (List.range n).map fun q : ℕ =>
        advanceLabeledHexEdge (source.1 + 1, source.2 - 3 * (q : ℤ) - 1)
          shadowC .c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hend := czLiteralBlock2_walkEnd_power source n
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, hend, czBlock2_reverse,
        List.range_succ, List.map_append]
      simp [walkPowerStart]
      congr 1
      apply Prod.ext <;> simp <;> ring

theorem czNoForward_power
    (block : List LabeledHexStep)
    (hsingle : ∀ source, forwardSideFiveEdges (walkLabeledHexEdges source block) = [])
    (source : HexVertex) (n : ℕ) :
    forwardSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower block n)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        forwardSideFiveEdges_append, ih, hsingle, List.nil_append]

theorem czNoReverse_power
    (block : List LabeledHexStep)
    (hsingle : ∀ source, reverseSideFiveEdges (walkLabeledHexEdges source block) = [])
    (source : HexVertex) (n : ℕ) :
    reverseSideFiveEdges
      (walkLabeledHexEdges source (labeledHexStepWordPower block n)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [labeledHexStepWordPower_succ, walkLabeledHexEdges_append,
        reverseSideFiveEdges_append, ih, hsingle, List.nil_append]

def czWalkForwardSideFiveCells (s r : ℕ) : List Cell :=
  (List.range r).map (fun q : ℕ =>
    ((r : ℤ) - 2 * q - 2, (s : ℤ) + q + 1)) ++
  (List.range r).map (fun q : ℕ =>
    ((s : ℤ) + q, (q : ℤ) - s - r + 1)) ++
  (List.range s).flatMap (fun q : ℕ =>
    [((s : ℤ) + r - q - 1, -(s : ℤ) + 2 * q + 1),
      ((s : ℤ) + r - q - 1, -(s : ℤ) + 2 * q + 2)])

def czWalkReverseSideFiveCells (s r : ℕ) : List Cell :=
  (List.range s).map (fun q : ℕ =>
    (-((r : ℤ)) - q, (s : ℤ) + r - q)) ++
  (List.range r).flatMap (fun q : ℕ =>
    [(-((s : ℤ)) - r + q, (r : ℤ) - 2 * q),
      (-((s : ℤ)) - r + q + 1, (r : ℤ) - 2 * q - 1)]) ++
  (List.range s).map (fun q : ℕ =>
    (-((s : ℤ)) + 1 + 2 * q, -((r : ℤ)) - q))

def czWalkForwardSideFiveEdges (s r : ℕ) : List LabeledHexEdge :=
  (czWalkForwardSideFiveCells s r).map fun cell => cellBoundaryEdgeAt cell .side₅

def czWalkReverseSideFiveEdges (s r : ℕ) : List LabeledHexEdge :=
  (czWalkReverseSideFiveCells s r).map fun cell =>
    reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)

theorem classZeroBoundaryWalk_forward (s r : ℕ) :
    forwardSideFiveEdges (classZeroLiteralBoundaryWalk s r) =
      czWalkForwardSideFiveEdges s r := by
  rw [classZeroLiteralBoundaryWalk_eq_segments]
  unfold classZeroBoundaryWalkBySegments
  simp only [forwardSideFiveEdges_append,
    czBlock5_forward_power,
    czNoForward_power czLiteralBlock4 czBlock4_forward,
    czNoForward_power czLiteralBlock3 czBlock3_forward,
    czNoForward_power czLiteralBlock2 czBlock2_forward,
    czBlock1_forward_power, czBlock0_forward_power,
    List.nil_append, List.append_nil]
  unfold czWalkForwardSideFiveEdges czWalkForwardSideFiveCells
  simp only [List.map_append, List.map_flatMap, List.map_map,
    Function.comp_apply, List.append_assoc]
  congr 1
  · apply List.map_congr_left
    intro q hq
    change advanceLabeledHexEdge
      ((czStage0 s r).1 - 1, (czStage0 s r).2 + 3 * (q : ℤ) + 2)
        shadowC.neg .c =
      cellBoundaryEdgeAt ((r : ℤ) - 2 * q - 2, (s : ℤ) + q + 1) .side₅
    rw [cellBoundaryEdgeAt_sideFive_formula]
    apply labeledHexEdge_ext <;> simp [czStage0] <;> ring
  · congr 1
    · apply List.map_congr_left
      intro q hq
      change advanceLabeledHexEdge
        ((czStage4 s r).1 + 3 * (q : ℤ) + 1, (czStage4 s r).2)
          shadowC.neg .c =
        cellBoundaryEdgeAt ((s : ℤ) + q, (q : ℤ) - s - r + 1) .side₅
      rw [cellBoundaryEdgeAt_sideFive_formula]
      apply labeledHexEdge_ext <;> simp [czStage4] <;> ring
    · apply List.flatMap_congr
      intro q hq
      simp only [List.map_cons, List.map_nil]
      apply congrArg₂ List.cons
      · rw [cellBoundaryEdgeAt_sideFive_formula]
        apply labeledHexEdge_ext <;> simp [czStage5] <;> ring
      · apply congrArg₂ List.cons
        · rw [cellBoundaryEdgeAt_sideFive_formula]
          apply labeledHexEdge_ext <;> simp [czStage5] <;> ring
        · rfl

theorem classZeroBoundaryWalk_reverse (s r : ℕ) :
    reverseSideFiveEdges (classZeroLiteralBoundaryWalk s r) =
      czWalkReverseSideFiveEdges s r := by
  rw [classZeroLiteralBoundaryWalk_eq_segments]
  unfold classZeroBoundaryWalkBySegments
  simp only [reverseSideFiveEdges_append,
    czNoReverse_power czLiteralBlock5 czBlock5_reverse,
    czBlock4_reverse_power, czBlock3_reverse_power,
    czBlock2_reverse_power,
    czNoReverse_power czLiteralBlock1 czBlock1_reverse,
    czNoReverse_power czLiteralBlock0 czBlock0_reverse,
    List.nil_append, List.append_nil]
  unfold czWalkReverseSideFiveEdges czWalkReverseSideFiveCells
  simp only [List.map_append, List.map_flatMap, List.map_map,
    Function.comp_apply, List.append_assoc]
  congr 1
  · apply List.map_congr_left
    intro q hq
    change advanceLabeledHexEdge
      ((czStage1 s r).1 - 3 * (q : ℤ), (czStage1 s r).2) shadowC .c =
      reverseLabeledHexEdge
        (cellBoundaryEdgeAt (-((r : ℤ)) - q, (s : ℤ) + r - q) .side₅)
    rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
    apply labeledHexEdge_ext <;> simp [czStage1] <;> ring
  · congr 1
    · apply List.flatMap_congr
      intro q hq
      simp only [List.map_cons, List.map_nil]
      apply congrArg₂ List.cons
      · rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
        apply labeledHexEdge_ext <;> simp [czStage2] <;> ring
      · apply congrArg₂ List.cons
        · rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
          apply labeledHexEdge_ext <;> simp [czStage2] <;> ring
        · rfl
    · apply List.map_congr_left
      intro q hq
      change advanceLabeledHexEdge
        ((czStage3 s r).1 + 1, (czStage3 s r).2 - 3 * (q : ℤ) - 1)
          shadowC .c =
        reverseLabeledHexEdge
          (cellBoundaryEdgeAt (-((s : ℤ)) + 1 + 2 * q, -((r : ℤ)) - q)
            .side₅)
      rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
      apply labeledHexEdge_ext <;> simp [czStage3] <;> ring

end FiniteDefects
