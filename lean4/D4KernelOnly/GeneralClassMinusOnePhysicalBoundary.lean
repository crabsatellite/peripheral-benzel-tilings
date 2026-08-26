import D4KernelOnly.GeneralShadowBoundary
import D4KernelOnly.D4LiteralBoundaryClosed

/-! # Physical class-minus-one benzel boundary for arbitrary side parameters -/

namespace FiniteDefects

open BenzelProblem6Kernel

def classMinusOneSourceBoundarySteps (s r : ℕ) : List D4LabeledStep :=
  labeledStepWordPower d4SourceStepBlock0 s ++ [(shadowA.neg, .a)] ++
  labeledStepWordPower d4SourceStepBlock1 r ++ [(shadowB, .b)] ++
  labeledStepWordPower d4SourceStepBlock2 s ++ [(shadowB.neg, .b)] ++
  labeledStepWordPower d4SourceStepBlock3 r ++ [(shadowC, .c)] ++
  labeledStepWordPower d4SourceStepBlock4 s ++ [(shadowC.neg, .c)] ++
  labeledStepWordPower d4SourceStepBlock5 r ++ [(shadowA, .a)]

theorem classMinusOneSourceBoundarySteps_labels (s r : ℕ) :
    (classMinusOneSourceBoundarySteps s r).map Prod.snd =
      classMinusOneSourceBoundaryLabels s r := by
  simp only [classMinusOneSourceBoundarySteps,
    classMinusOneSourceBoundaryLabels,
    List.map_append, List.map_singleton, labeledStepWordPower_map_snd]
  simp [d4SourceStepBlock0, d4SourceStepBlock1,
    d4SourceStepBlock2, d4SourceStepBlock3,
    d4SourceStepBlock4, d4SourceStepBlock5,
    d4BoundaryBlock0, d4BoundaryBlock1, d4BoundaryBlock2,
    d4BoundaryBlock3, d4BoundaryBlock4, d4BoundaryBlock5]

def classMinusOneReflectedReversedBoundarySteps (s r : ℕ) :
    List D4LabeledStep :=
  ((classMinusOneSourceBoundarySteps s r).map reflectD4LabeledStep).reverse.map
    reverseD4LabeledStep

def classMinusOneLiteralBoundarySteps (s r : ℕ) : List D4LabeledStep :=
  rotateHeadToTail (classMinusOneReflectedReversedBoundarySteps s r)

theorem classMinusOneReflectedReversedBoundarySteps_labels (s r : ℕ) :
    (classMinusOneReflectedReversedBoundarySteps s r).map Prod.snd =
      classMinusOneReflectedReversedBoundaryLabels s r := by
  have hsource := congrArg (List.map swapABShadowLabel)
    (classMinusOneSourceBoundarySteps_labels s r)
  have hreverse := congrArg List.reverse hsource
  simpa [classMinusOneReflectedReversedBoundarySteps,
    classMinusOneReflectedReversedBoundaryLabels, reflectD4LabeledStep,
    reverseD4LabeledStep, List.map_reverse, List.map_map,
    Function.comp_def] using hreverse

theorem classMinusOneLiteralBoundarySteps_labels (s r : ℕ) :
    (classMinusOneLiteralBoundarySteps s r).map Prod.snd =
      classMinusOneLiteralBoundaryLabels s r := by
  rw [classMinusOneLiteralBoundarySteps,
    classMinusOneLiteralBoundaryLabels,
    map_snd_rotateHeadToTail,
    classMinusOneReflectedReversedBoundarySteps_labels]

def classMinusOneLiteralBoundaryRoot (s r : ℕ) : HexVertex :=
  ((r : ℤ) - s, 2 * (r : ℤ) + s)

def classMinusOneLiteralBoundaryWalk (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (classMinusOneLiteralBoundaryRoot s r)
    (classMinusOneLiteralBoundarySteps s r)

theorem classMinusOneLiteralBoundaryWalk_labels (s r : ℕ) :
    labeledEdgeWord (classMinusOneLiteralBoundaryWalk s r) =
      classMinusOneLiteralBoundaryLabels s r := by
  rw [classMinusOneLiteralBoundaryWalk, labeledEdgeWord_walk,
    classMinusOneLiteralBoundarySteps_labels]

theorem classMinusOneSourceBoundarySteps_closed (s r : ℕ) :
    let summary := shadowWordSummary
      ((classMinusOneSourceBoundarySteps s r).map Prod.fst)
    summary.x = 0 ∧ summary.y = 0 := by
  simp only [classMinusOneSourceBoundarySteps, List.map_append,
    List.map_singleton, labeledStepWordPower_map_fst,
    shadowWordSummary_append, shadowWordSummary_power,
    d4SourceStepBlock0_summary, d4SourceStepBlock1_summary,
    d4SourceStepBlock2_summary, d4SourceStepBlock3_summary,
    d4SourceStepBlock4_summary, d4SourceStepBlock5_summary,
    shadowWordSummary, ShadowSummary.empty, ShadowSummary.single,
    ShadowSummary.scale, ShadowSummary.append,
    ShadowSummary.displacement, shadowCross,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  constructor <;> push_cast <;> ring

theorem classMinusOneReflectedReversedBoundarySteps_vectors (s r : ℕ) :
    (classMinusOneReflectedReversedBoundarySteps s r).map Prod.fst =
      (((classMinusOneSourceBoundarySteps s r).map Prod.fst).map
        swapABShadowFrame.apply).reverse.map ShadowStep.neg := by
  simp [classMinusOneReflectedReversedBoundarySteps, reflectD4LabeledStep,
    reverseD4LabeledStep, List.map_reverse, List.map_map,
    Function.comp_def]

theorem classMinusOneReflectedReversedBoundarySteps_closed (s r : ℕ) :
    let summary := shadowWordSummary
      ((classMinusOneReflectedReversedBoundarySteps s r).map Prod.fst)
    summary.x = 0 ∧ summary.y = 0 := by
  rw [classMinusOneReflectedReversedBoundarySteps_vectors,
    shadowWordSummary_reverse_neg,
    shadowWordSummary_map_frame]
  have hsource := classMinusOneSourceBoundarySteps_closed s r
  rcases hsummary : shadowWordSummary
      ((classMinusOneSourceBoundarySteps s r).map Prod.fst) with
    ⟨x, y, area⟩
  rw [hsummary] at hsource
  dsimp at hsource
  simp [swapABShadowFrame, ShadowSummary.displacement, ShadowFrame.apply,
    hsource.1, hsource.2]

theorem classMinusOneLiteralBoundarySteps_closed (s r : ℕ) :
    let summary := shadowWordSummary
      ((classMinusOneLiteralBoundarySteps s r).map Prod.fst)
    summary.x = 0 ∧ summary.y = 0 := by
  rw [classMinusOneLiteralBoundarySteps, map_snd_rotateHeadToTail]
  exact rotateHeadToTail_closed _
    (classMinusOneReflectedReversedBoundarySteps_closed s r)

theorem classMinusOneLiteralBoundary_walkEnd (s r : ℕ) :
    labeledHexWalkEnd (classMinusOneLiteralBoundaryRoot s r)
        (classMinusOneLiteralBoundarySteps s r) =
      classMinusOneLiteralBoundaryRoot s r := by
  rw [labeledHexWalkEnd_eq_summary]
  have hclosed := classMinusOneLiteralBoundarySteps_closed s r
  rw [hclosed.1, hclosed.2]
  simp

theorem classMinusOneLiteralBoundary_continuous (s r : ℕ) :
    ContinuousLabeledEdgePath (classMinusOneLiteralBoundaryRoot s r)
      (classMinusOneLiteralBoundaryWalk s r)
      (classMinusOneLiteralBoundaryRoot s r) := by
  unfold classMinusOneLiteralBoundaryWalk
  simpa [classMinusOneLiteralBoundary_walkEnd] using
    walkLabeledHexEdges_continuous
      (classMinusOneLiteralBoundaryRoot s r)
      (classMinusOneLiteralBoundarySteps s r)

end FiniteDefects
