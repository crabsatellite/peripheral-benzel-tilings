import D4KernelOnly.D4LiteralBoundaryWalk

/-! # Closure of the physical d=4 boundary walk -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem labeledStepWordPower_map_fst
    (word : List D4LabeledStep) (exponent : ℕ) :
    (labeledStepWordPower word exponent).map Prod.fst =
      shadowWordPower (word.map Prod.fst) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, shadowWordPower_succ,
        List.map_append, ih]

theorem d4SourceStepBlock0_summary :
    shadowWordSummary (d4SourceStepBlock0.map Prod.fst) =
      ⟨0, 3, -3⟩ := by decide

theorem d4SourceStepBlock1_summary :
    shadowWordSummary (d4SourceStepBlock1.map Prod.fst) =
      ⟨-3, 0, 3⟩ := by decide

theorem d4SourceStepBlock2_summary :
    shadowWordSummary (d4SourceStepBlock2.map Prod.fst) =
      ⟨-3, -3, -3⟩ := by decide

theorem d4SourceStepBlock3_summary :
    shadowWordSummary (d4SourceStepBlock3.map Prod.fst) =
      ⟨0, -3, 3⟩ := by decide

theorem d4SourceStepBlock4_summary :
    shadowWordSummary (d4SourceStepBlock4.map Prod.fst) =
      ⟨3, 0, -3⟩ := by decide

theorem d4SourceStepBlock5_summary :
    shadowWordSummary (d4SourceStepBlock5.map Prod.fst) =
      ⟨3, 3, 3⟩ := by decide

theorem d4SourceBoundarySteps_summary (m : ℕ) :
    shadowWordSummary ((d4SourceBoundarySteps m).map Prod.fst) =
      ⟨0, 0, 9 * (m : ℤ) ^ 2 + 63 * (m : ℤ) + 72⟩ := by
  simp only [d4SourceBoundarySteps, List.map_append,
    List.map_singleton, labeledStepWordPower_map_fst,
    shadowWordSummary_append, shadowWordSummary_power,
    d4SourceStepBlock0_summary, d4SourceStepBlock1_summary,
    d4SourceStepBlock2_summary, d4SourceStepBlock3_summary,
    d4SourceStepBlock4_summary, d4SourceStepBlock5_summary,
    shadowWordSummary, ShadowSummary.empty, ShadowSummary.single,
    ShadowSummary.scale, ShadowSummary.append,
    ShadowSummary.displacement, shadowCross,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  apply shadowSummary_ext
  all_goals push_cast
  all_goals ring

theorem d4ReflectedReversedBoundarySteps_vectors (m : ℕ) :
    (d4ReflectedReversedBoundarySteps m).map Prod.fst =
      (((d4SourceBoundarySteps m).map Prod.fst).map
        swapABShadowFrame.apply).reverse.map ShadowStep.neg := by
  simp [d4ReflectedReversedBoundarySteps, reflectD4LabeledStep,
    reverseD4LabeledStep, List.map_reverse, List.map_map,
    Function.comp_def]

theorem d4ReflectedReversedBoundarySteps_closed (m : ℕ) :
    let summary := shadowWordSummary
      ((d4ReflectedReversedBoundarySteps m).map Prod.fst)
    summary.x = 0 ∧ summary.y = 0 := by
  rw [d4ReflectedReversedBoundarySteps_vectors,
    shadowWordSummary_reverse_neg,
    shadowWordSummary_map_frame,
    d4SourceBoundarySteps_summary]
  simp [ShadowSummary.displacement, ShadowFrame.apply]

theorem rotateHeadToTail_closed
    (items : List ShadowStep)
    (hclosed : (shadowWordSummary items).x = 0 ∧
      (shadowWordSummary items).y = 0) :
    let summary := shadowWordSummary (rotateHeadToTail items)
    summary.x = 0 ∧ summary.y = 0 := by
  cases items with
  | nil =>
      simp [rotateHeadToTail, shadowWordSummary, ShadowSummary.empty]
  | cons head tail =>
      simp only [rotateHeadToTail, shadowWordSummary_append,
        shadowWordSummary, ShadowSummary.single,
        ShadowSummary.empty, ShadowSummary.append,
        ShadowSummary.displacement] at hclosed ⊢
      constructor <;> omega

theorem d4LiteralBoundarySteps_vectors (m : ℕ) :
    (d4LiteralBoundarySteps m).map Prod.fst =
      rotateHeadToTail
        ((d4ReflectedReversedBoundarySteps m).map Prod.fst) := by
  rw [d4LiteralBoundarySteps, map_snd_rotateHeadToTail]

theorem d4LiteralBoundarySteps_closed (m : ℕ) :
    let summary := shadowWordSummary
      ((d4LiteralBoundarySteps m).map Prod.fst)
    summary.x = 0 ∧ summary.y = 0 := by
  rw [d4LiteralBoundarySteps_vectors]
  exact rotateHeadToTail_closed _
    (d4ReflectedReversedBoundarySteps_closed m)

theorem labeledHexWalkEnd_eq_summary (source : HexVertex)
    (steps : List D4LabeledStep) :
    labeledHexWalkEnd source steps =
      (source.1 + (shadowWordSummary (steps.map Prod.fst)).x,
        source.2 + (shadowWordSummary (steps.map Prod.fst)).y) := by
  induction steps generalizing source with
  | nil =>
      simp [labeledHexWalkEnd, shadowWordSummary, ShadowSummary.empty]
  | cons step rest ih =>
      rw [labeledHexWalkEnd]
      rw [ih]
      simp only [List.map_cons, shadowWordSummary,
        ShadowSummary.single, ShadowSummary.append,
        ShadowSummary.displacement, addHexStep]
      apply Prod.ext <;> simp <;> ring

theorem d4LiteralBoundary_walkEnd (m : ℕ) :
    labeledHexWalkEnd (d4LiteralBoundaryRoot m)
        (d4LiteralBoundarySteps m) =
      d4LiteralBoundaryRoot m := by
  rw [labeledHexWalkEnd_eq_summary]
  have hclosed := d4LiteralBoundarySteps_closed m
  rw [hclosed.1, hclosed.2]
  simp

theorem d4LiteralBoundary_continuous (m : ℕ) :
    ContinuousLabeledEdgePath (d4LiteralBoundaryRoot m)
      (d4LiteralBoundaryWalk m) (d4LiteralBoundaryRoot m) := by
  unfold d4LiteralBoundaryWalk
  simpa [d4LiteralBoundary_walkEnd] using
    walkLabeledHexEdges_continuous
      (d4LiteralBoundaryRoot m) (d4LiteralBoundarySteps m)

end FiniteDefects
