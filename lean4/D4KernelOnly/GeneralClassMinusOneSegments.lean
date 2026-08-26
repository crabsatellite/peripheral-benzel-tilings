import D4KernelOnly.GeneralClassMinusOnePhysicalBoundary
import D4KernelOnly.D4BoundaryWalkPower
import D4KernelOnly.D4BoundarySideFiveOccurrences

/-! # Segment normal form for the general class-minus-one boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem transformedBoundaryPower
    (source literal : List D4LabeledStep)
    (hblock : transformD4BoundaryWord source = literal)
    (exponent : ℕ) :
    ((labeledStepWordPower source exponent).map
      transformD4BoundaryStep).reverse =
      labeledStepWordPower literal exponent := by
  rw [← List.map_reverse]
  change transformD4BoundaryWord (labeledStepWordPower source exponent) = _
  rw [transformD4BoundaryWord_power, hblock]

def classMinusOneLiteralBoundaryStepsExplicit (s r : ℕ) :
    List D4LabeledStep :=
  labeledStepWordPower d4LiteralStepBlock5 r ++
  ([(shadowC, .c)] ++
  (labeledStepWordPower d4LiteralStepBlock4 s ++
  ([(shadowC.neg, .c)] ++
  (labeledStepWordPower d4LiteralStepBlock3 r ++
  ([(shadowA, .a)] ++
  (labeledStepWordPower d4LiteralStepBlock2 s ++
  ([(shadowA.neg, .a)] ++
  (labeledStepWordPower d4LiteralStepBlock1 r ++
  ([(shadowB, .b)] ++
  (labeledStepWordPower d4LiteralStepBlock0 s ++
    [(shadowB.neg, .b)]))))))))))

theorem classMinusOneLiteralBoundarySteps_eq_explicit (s r : ℕ) :
    classMinusOneLiteralBoundarySteps s r =
      classMinusOneLiteralBoundaryStepsExplicit s r := by
  have h0 := transformedBoundaryPower d4SourceStepBlock0 d4LiteralStepBlock0
    transformD4SourceBlock0 s
  have h1 := transformedBoundaryPower d4SourceStepBlock1 d4LiteralStepBlock1
    transformD4SourceBlock1 r
  have h2 := transformedBoundaryPower d4SourceStepBlock2 d4LiteralStepBlock2
    transformD4SourceBlock2 s
  have h3 := transformedBoundaryPower d4SourceStepBlock3 d4LiteralStepBlock3
    transformD4SourceBlock3 r
  have h4 := transformedBoundaryPower d4SourceStepBlock4 d4LiteralStepBlock4
    transformD4SourceBlock4 s
  have h5 := transformedBoundaryPower d4SourceStepBlock5 d4LiteralStepBlock5
    transformD4SourceBlock5 r
  simp only [classMinusOneLiteralBoundarySteps,
    classMinusOneReflectedReversedBoundarySteps,
    classMinusOneSourceBoundarySteps,
    transformD4BoundaryWord, List.reverse_append, List.map_append,
    List.reverse_singleton, List.map_singleton,
    reverse_reflectD4BoundaryWord,
    transformD4Separator0, transformD4Separator1,
    transformD4Separator2, transformD4Separator3,
    transformD4Separator4, transformD4Separator5,
    classMinusOneLiteralBoundaryStepsExplicit]
  simp only [List.map_reverse]
  rw [h5, h4, h3, h2, h1, h0]
  simp [rotateHeadToTail, reflectD4LabeledStep, reverseD4LabeledStep,
    swapABShadowFrame, swapABShadowLabel, ShadowFrame.apply,
    shadowA, shadowB, shadowC, ShadowStep.neg,
    labeledStepWordPower_commute]

theorem generalLiteralBlock4_walkEnd_power
    (source : HexVertex) (exponent : ℕ) :
    labeledHexWalkEnd source
        (labeledStepWordPower d4LiteralStepBlock4 exponent) =
      walkPowerStart source (0, -3) exponent := by
  exact labeledHexWalkEnd_power d4LiteralStepBlock4 (0, -3) source
    (fun start => by simpa using d4LiteralBlock4_walkEnd start) exponent

theorem generalLiteralBlock2_walkEnd_power
    (source : HexVertex) (exponent : ℕ) :
    labeledHexWalkEnd source
        (labeledStepWordPower d4LiteralStepBlock2 exponent) =
      walkPowerStart source (3, 3) exponent := by
  exact labeledHexWalkEnd_power d4LiteralStepBlock2 (3, 3) source
    (fun start => by simpa using d4LiteralBlock2_walkEnd start) exponent

theorem generalLiteralBlock0_walkEnd_power
    (source : HexVertex) (exponent : ℕ) :
    labeledHexWalkEnd source
        (labeledStepWordPower d4LiteralStepBlock0 exponent) =
      walkPowerStart source (-3, 0) exponent := by
  exact labeledHexWalkEnd_power d4LiteralStepBlock0 (-3, 0) source
    (fun start => by simpa using d4LiteralBlock0_walkEnd start) exponent

def cmoStage0 (s r : ℕ) : HexVertex := ((r : ℤ) - s, 2 * (r : ℤ) + s)
def cmoStage1 (s r : ℕ) : HexVertex := (-2 * (r : ℤ) - s, (s : ℤ) - r)
def cmoStage2 (s r : ℕ) : HexVertex := (-2 * (r : ℤ) - s - 1, (s : ℤ) - r - 1)
def cmoStage3 (s r : ℕ) : HexVertex := (-2 * (r : ℤ) - s - 1, -2 * (s : ℤ) - r - 1)
def cmoStage4 (s r : ℕ) : HexVertex := (-2 * (r : ℤ) - s, -2 * (s : ℤ) - r)
def cmoStage5 (s r : ℕ) : HexVertex := ((r : ℤ) - s, -2 * (s : ℤ) - r)
def cmoStage6 (s r : ℕ) : HexVertex := ((r : ℤ) - s + 1, -2 * (s : ℤ) - r)
def cmoStage7 (s r : ℕ) : HexVertex := ((r : ℤ) + 2 * s + 1, (s : ℤ) - r)
def cmoStage8 (s r : ℕ) : HexVertex := ((r : ℤ) + 2 * s, (s : ℤ) - r)
def cmoStage9 (s r : ℕ) : HexVertex := ((r : ℤ) + 2 * s, (s : ℤ) + 2 * r)
def cmoStage10 (s r : ℕ) : HexVertex := ((r : ℤ) + 2 * s, (s : ℤ) + 2 * r + 1)
def cmoStage11 (s r : ℕ) : HexVertex := ((r : ℤ) - s, (s : ℤ) + 2 * r + 1)

theorem cmoStage0_eq_root (s r : ℕ) :
    cmoStage0 s r = classMinusOneLiteralBoundaryRoot s r := rfl

theorem cmoStage1_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage0 s r)
      (labeledStepWordPower d4LiteralStepBlock5 r) = cmoStage1 s r := by
  rw [d4LiteralBlock5_walkEnd_power]
  apply Prod.ext <;> simp [cmoStage0, cmoStage1, walkPowerStart] <;> ring

theorem cmoStage2_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage1 s r) [(shadowC, .c)] = cmoStage2 s r := by
  apply Prod.ext <;> simp [cmoStage1, cmoStage2, labeledHexWalkEnd,
    addHexStep, shadowC] <;> ring

theorem cmoStage3_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage2 s r)
      (labeledStepWordPower d4LiteralStepBlock4 s) = cmoStage3 s r := by
  rw [generalLiteralBlock4_walkEnd_power]
  apply Prod.ext <;> simp [cmoStage2, cmoStage3, walkPowerStart] <;> ring

theorem cmoStage4_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage3 s r) [(shadowC.neg, .c)] = cmoStage4 s r := by
  apply Prod.ext <;> simp [cmoStage3, cmoStage4, labeledHexWalkEnd,
    addHexStep, shadowC, ShadowStep.neg] <;> ring

theorem cmoStage5_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage4 s r)
      (labeledStepWordPower d4LiteralStepBlock3 r) = cmoStage5 s r := by
  rw [d4LiteralBlock3_walkEnd_power]
  apply Prod.ext <;> simp [cmoStage4, cmoStage5, walkPowerStart] <;> ring

theorem cmoStage6_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage5 s r) [(shadowA, .a)] = cmoStage6 s r := by
  apply Prod.ext <;> simp [cmoStage5, cmoStage6, labeledHexWalkEnd,
    addHexStep, shadowA] <;> ring

theorem cmoStage7_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage6 s r)
      (labeledStepWordPower d4LiteralStepBlock2 s) = cmoStage7 s r := by
  rw [generalLiteralBlock2_walkEnd_power]
  apply Prod.ext <;> simp [cmoStage6, cmoStage7, walkPowerStart] <;> ring

theorem cmoStage8_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage7 s r) [(shadowA.neg, .a)] = cmoStage8 s r := by
  apply Prod.ext <;> simp [cmoStage7, cmoStage8, labeledHexWalkEnd,
    addHexStep, shadowA, ShadowStep.neg] <;> ring

theorem cmoStage9_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage8 s r)
      (labeledStepWordPower d4LiteralStepBlock1 r) = cmoStage9 s r := by
  rw [d4LiteralBlock1_walkEnd_power]
  apply Prod.ext <;> simp [cmoStage8, cmoStage9, walkPowerStart] <;> ring

theorem cmoStage10_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage9 s r) [(shadowB, .b)] = cmoStage10 s r := by
  apply Prod.ext <;> simp [cmoStage9, cmoStage10, labeledHexWalkEnd,
    addHexStep, shadowB] <;> ring

theorem cmoStage11_eq (s r : ℕ) :
    labeledHexWalkEnd (cmoStage10 s r)
      (labeledStepWordPower d4LiteralStepBlock0 s) = cmoStage11 s r := by
  rw [generalLiteralBlock0_walkEnd_power]
  apply Prod.ext <;> simp [cmoStage10, cmoStage11, walkPowerStart] <;> ring

def classMinusOneBoundaryWalkBySegments (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (cmoStage0 s r)
      (labeledStepWordPower d4LiteralStepBlock5 r) ++
  (walkLabeledHexEdges (cmoStage1 s r) [(shadowC, .c)] ++
  (walkLabeledHexEdges (cmoStage2 s r)
      (labeledStepWordPower d4LiteralStepBlock4 s) ++
  (walkLabeledHexEdges (cmoStage3 s r) [(shadowC.neg, .c)] ++
  (walkLabeledHexEdges (cmoStage4 s r)
      (labeledStepWordPower d4LiteralStepBlock3 r) ++
  (walkLabeledHexEdges (cmoStage5 s r) [(shadowA, .a)] ++
  (walkLabeledHexEdges (cmoStage6 s r)
      (labeledStepWordPower d4LiteralStepBlock2 s) ++
  (walkLabeledHexEdges (cmoStage7 s r) [(shadowA.neg, .a)] ++
  (walkLabeledHexEdges (cmoStage8 s r)
      (labeledStepWordPower d4LiteralStepBlock1 r) ++
  (walkLabeledHexEdges (cmoStage9 s r) [(shadowB, .b)] ++
  (walkLabeledHexEdges (cmoStage10 s r)
      (labeledStepWordPower d4LiteralStepBlock0 s) ++
    walkLabeledHexEdges (cmoStage11 s r) [(shadowB.neg, .b)]))))))))))

theorem classMinusOneLiteralBoundaryWalk_eq_segments (s r : ℕ) :
    classMinusOneLiteralBoundaryWalk s r =
      classMinusOneBoundaryWalkBySegments s r := by
  rw [classMinusOneLiteralBoundaryWalk,
    classMinusOneLiteralBoundarySteps_eq_explicit]
  unfold classMinusOneLiteralBoundaryStepsExplicit
  rw [← cmoStage0_eq_root]
  rw [walkLabeledHexEdges_append, cmoStage1_eq]
  rw [walkLabeledHexEdges_append, cmoStage2_eq]
  rw [walkLabeledHexEdges_append, cmoStage3_eq]
  rw [walkLabeledHexEdges_append, cmoStage4_eq]
  rw [walkLabeledHexEdges_append, cmoStage5_eq]
  rw [walkLabeledHexEdges_append, cmoStage6_eq]
  rw [walkLabeledHexEdges_append, cmoStage7_eq]
  rw [walkLabeledHexEdges_append, cmoStage8_eq]
  rw [walkLabeledHexEdges_append, cmoStage9_eq]
  rw [walkLabeledHexEdges_append, cmoStage10_eq]
  rw [walkLabeledHexEdges_append, cmoStage11_eq]
  rfl

end FiniteDefects
