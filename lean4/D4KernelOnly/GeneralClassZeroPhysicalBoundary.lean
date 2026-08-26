import D4KernelOnly.GeneralShadowBoundary
import D4KernelOnly.D4LiteralBoundaryClosed
import BenzelProblem6Kernel.LiteralPeripheralBoundaryWalk

/-! # Physical class-zero benzel boundary for arbitrary side parameters -/

namespace FiniteDefects

open BenzelProblem6Kernel

def classZeroClockwiseSteps (s r : ℕ) : List LabeledHexStep :=
  labeledHexStepWordPower literalPeripheralBlock₀ s ++
  labeledHexStepWordPower literalPeripheralBlock₁ r ++
  labeledHexStepWordPower literalPeripheralBlock₂ s ++
  labeledHexStepWordPower literalPeripheralBlock₃ r ++
  labeledHexStepWordPower literalPeripheralBlock₄ s ++
  labeledHexStepWordPower literalPeripheralBlock₅ r

def classZeroClockwiseRoot (s r : ℕ) : HexVertex :=
  (2 * (s : ℤ) + r, (s : ℤ) - r)

def classZeroClockwiseBoundary (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (classZeroClockwiseRoot s r) (classZeroClockwiseSteps s r)

def reverseClassZeroStep (step : LabeledHexStep) : LabeledHexStep :=
  (step.1.neg, step.2)

def classZeroLiteralBoundarySteps (s r : ℕ) : List LabeledHexStep :=
  (classZeroClockwiseSteps s r).reverse.map reverseClassZeroStep

def classZeroLiteralBoundaryWalk (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (classZeroClockwiseRoot s r)
    (classZeroLiteralBoundarySteps s r)

def classZeroLiteralBoundaryLabels (s r : ℕ) : List ShadowLabel :=
  mirrorReverseShadowWord (classZeroBoundaryLabels s r)

theorem classZeroClockwiseSteps_labels (s r : ℕ) :
    (classZeroClockwiseSteps s r).map Prod.snd =
      (classZeroBoundaryLabels s r).map mirrorShadowLabel := by
  simp only [classZeroClockwiseSteps, classZeroBoundaryLabels,
    List.map_append, labeledHexStepWordPower_labels,
    literalPeripheralBlock₀_labels, literalPeripheralBlock₁_labels,
    literalPeripheralBlock₂_labels, literalPeripheralBlock₃_labels,
    literalPeripheralBlock₄_labels, literalPeripheralBlock₅_labels,
    List.map_map, shadowLabelWordPower_map_mirror]

theorem classZeroLiteralBoundaryWalk_labels (s r : ℕ) :
    labeledEdgeWord (classZeroLiteralBoundaryWalk s r) =
      classZeroLiteralBoundaryLabels s r := by
  rw [classZeroLiteralBoundaryWalk, labeledEdgeWord_walk]
  unfold classZeroLiteralBoundarySteps classZeroLiteralBoundaryLabels
  simp only [List.map_map, List.map_reverse]
  have hmap : (classZeroClockwiseSteps s r).map
      (Prod.snd ∘ reverseClassZeroStep) =
      (classZeroClockwiseSteps s r).map Prod.snd := by
    apply List.map_congr_left
    intro step hstep
    rfl
  rw [hmap]
  rw [classZeroClockwiseSteps_labels]
  rfl

theorem labeledHexStepWordPower_map_fst
    (word : List LabeledHexStep) (exponent : ℕ) :
    (labeledHexStepWordPower word exponent).map Prod.fst =
      shadowWordPower (word.map Prod.fst) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledHexStepWordPower_succ,
        shadowWordPower_succ, List.map_append, ih]

theorem classZeroClockwiseSteps_closed (s r : ℕ) :
    let summary := shadowWordSummary ((classZeroClockwiseSteps s r).map Prod.fst)
    summary.x = 0 ∧ summary.y = 0 := by
  simp only [classZeroClockwiseSteps, List.map_append,
    labeledHexStepWordPower_map_fst, shadowWordSummary_append,
    shadowWordSummary_power]
  simp [literalPeripheralBlock₀, literalPeripheralBlock₁,
    literalPeripheralBlock₂, literalPeripheralBlock₃,
    literalPeripheralBlock₄, literalPeripheralBlock₅,
    shadowWordSummary, ShadowSummary.empty, ShadowSummary.single,
    ShadowSummary.scale, ShadowSummary.append,
    ShadowSummary.displacement, shadowCross,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem classZeroClockwise_walkEnd (s r : ℕ) :
    labeledHexWalkEnd (classZeroClockwiseRoot s r) (classZeroClockwiseSteps s r) =
      classZeroClockwiseRoot s r := by
  rw [labeledHexWalkEnd_eq_summary]
  have hclosed := classZeroClockwiseSteps_closed s r
  rw [hclosed.1, hclosed.2]
  simp

theorem classZeroClockwise_continuous (s r : ℕ) :
    ContinuousLabeledEdgePath (classZeroClockwiseRoot s r)
      (classZeroClockwiseBoundary s r) (classZeroClockwiseRoot s r) := by
  unfold classZeroClockwiseBoundary
  simpa [classZeroClockwise_walkEnd] using
    walkLabeledHexEdges_continuous
      (classZeroClockwiseRoot s r) (classZeroClockwiseSteps s r)

theorem classZeroLiteralBoundarySteps_closed (s r : ℕ) :
    let summary := shadowWordSummary
      ((classZeroLiteralBoundarySteps s r).map Prod.fst)
    summary.x = 0 ∧ summary.y = 0 := by
  unfold classZeroLiteralBoundarySteps
  have hvectors :
      ((classZeroClockwiseSteps s r).reverse.map reverseClassZeroStep).map
          Prod.fst =
        ((classZeroClockwiseSteps s r).map Prod.fst).reverse.map ShadowStep.neg := by
    simp [List.map_reverse, List.map_map, Function.comp_def,
      reverseClassZeroStep]
  rw [hvectors, shadowWordSummary_reverse_neg]
  have hclosed := classZeroClockwiseSteps_closed s r
  rcases hsummary : shadowWordSummary
      ((classZeroClockwiseSteps s r).map Prod.fst) with ⟨x, y, area⟩
  rw [hsummary] at hclosed
  dsimp at hclosed ⊢
  omega

theorem classZeroLiteralBoundary_walkEnd (s r : ℕ) :
    labeledHexWalkEnd (classZeroClockwiseRoot s r)
        (classZeroLiteralBoundarySteps s r) =
      classZeroClockwiseRoot s r := by
  rw [labeledHexWalkEnd_eq_summary]
  have hclosed := classZeroLiteralBoundarySteps_closed s r
  rw [hclosed.1, hclosed.2]
  simp

theorem classZeroLiteralBoundary_continuous (s r : ℕ) :
    ContinuousLabeledEdgePath (classZeroClockwiseRoot s r)
      (classZeroLiteralBoundaryWalk s r) (classZeroClockwiseRoot s r) := by
  unfold classZeroLiteralBoundaryWalk
  simpa [classZeroLiteralBoundary_walkEnd] using
    walkLabeledHexEdges_continuous
      (classZeroClockwiseRoot s r) (classZeroLiteralBoundarySteps s r)

theorem classZeroBoundary_identityWord (s r : ℕ) :
    IdentityShadowWord (classZeroBoundaryLabels s r)
      (9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
        (r : ℤ) ^ 2 - (s : ℤ) - (r : ℤ))) := by
  refine ⟨classZeroBoundary_finalFrame_identity s r, ?_⟩
  have h := classZeroBoundary_identityFrame_summary s r
  ring_nf at h ⊢
  exact h

theorem classZeroLiteralBoundary_identityWord (s r : ℕ) :
    IdentityShadowWord (classZeroLiteralBoundaryLabels s r)
      (9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
        (r : ℤ) ^ 2 - (s : ℤ) - (r : ℤ))) :=
  identityShadowWord_mirrorReverse (classZeroBoundary_identityWord s r)

end FiniteDefects
