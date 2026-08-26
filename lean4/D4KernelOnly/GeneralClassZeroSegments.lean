import D4KernelOnly.GeneralClassZeroPhysicalBoundary
import D4KernelOnly.D4BoundaryWalkPower

/-! # Segment normal form for the general class-zero boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

theorem labeledHexStepWordPower_eq_labeledStepWordPower
    (word : List LabeledHexStep) (n : ℕ) :
    labeledHexStepWordPower word n = labeledStepWordPower word n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [labeledHexStepWordPower_succ, labeledStepWordPower_succ, ih]

theorem labeledHexStepWordPower_commute
    (word : List LabeledHexStep) (n : ℕ) :
    word ++ labeledHexStepWordPower word n =
      labeledHexStepWordPower word n ++ word := by
  rw [labeledHexStepWordPower_eq_labeledStepWordPower,
    labeledStepWordPower_commute]

def reverseClassZeroWord (word : List LabeledHexStep) : List LabeledHexStep :=
  word.reverse.map reverseClassZeroStep

def czLiteralBlock0 := reverseClassZeroWord literalPeripheralBlock₀
def czLiteralBlock1 := reverseClassZeroWord literalPeripheralBlock₁
def czLiteralBlock2 := reverseClassZeroWord literalPeripheralBlock₂
def czLiteralBlock3 := reverseClassZeroWord literalPeripheralBlock₃
def czLiteralBlock4 := reverseClassZeroWord literalPeripheralBlock₄
def czLiteralBlock5 := reverseClassZeroWord literalPeripheralBlock₅

theorem reverseClassZeroWord_power
    (word : List LabeledHexStep) (exponent : ℕ) :
    reverseClassZeroWord (labeledHexStepWordPower word exponent) =
      labeledHexStepWordPower (reverseClassZeroWord word) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledHexStepWordPower_succ, reverseClassZeroWord,
        List.reverse_append, List.map_append]
      change reverseClassZeroWord word ++
        reverseClassZeroWord (labeledHexStepWordPower word exponent) = _
      rw [ih, labeledHexStepWordPower_succ]
      exact labeledHexStepWordPower_commute _ _

def classZeroLiteralBoundaryStepsExplicit (s r : ℕ) : List LabeledHexStep :=
  labeledHexStepWordPower czLiteralBlock5 r ++
  (labeledHexStepWordPower czLiteralBlock4 s ++
  (labeledHexStepWordPower czLiteralBlock3 r ++
  (labeledHexStepWordPower czLiteralBlock2 s ++
  (labeledHexStepWordPower czLiteralBlock1 r ++
    labeledHexStepWordPower czLiteralBlock0 s))))

theorem classZeroLiteralBoundarySteps_eq_explicit (s r : ℕ) :
    classZeroLiteralBoundarySteps s r =
      classZeroLiteralBoundaryStepsExplicit s r := by
  simp only [classZeroLiteralBoundarySteps, classZeroClockwiseSteps,
    List.reverse_append, List.map_append,
    classZeroLiteralBoundaryStepsExplicit]
  change reverseClassZeroWord (labeledHexStepWordPower literalPeripheralBlock₅ r) ++
    (reverseClassZeroWord (labeledHexStepWordPower literalPeripheralBlock₄ s) ++
    (reverseClassZeroWord (labeledHexStepWordPower literalPeripheralBlock₃ r) ++
    (reverseClassZeroWord (labeledHexStepWordPower literalPeripheralBlock₂ s) ++
    (reverseClassZeroWord (labeledHexStepWordPower literalPeripheralBlock₁ r) ++
      reverseClassZeroWord (labeledHexStepWordPower literalPeripheralBlock₀ s))))) = _
  rw [reverseClassZeroWord_power, reverseClassZeroWord_power,
    reverseClassZeroWord_power, reverseClassZeroWord_power,
    reverseClassZeroWord_power, reverseClassZeroWord_power]
  rfl

theorem czLiteralBlock5_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source czLiteralBlock5 = (source.1, source.2 + 3) := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock5, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₅, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czLiteralBlock4_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source czLiteralBlock4 = (source.1 - 3, source.2) := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock4, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₄, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czLiteralBlock3_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source czLiteralBlock3 = (source.1 - 3, source.2 - 3) := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock3, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₃, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czLiteralBlock2_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source czLiteralBlock2 = (source.1, source.2 - 3) := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock2, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₂, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czLiteralBlock1_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source czLiteralBlock1 = (source.1 + 3, source.2) := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock1, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₁, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czLiteralBlock0_walkEnd (source : HexVertex) :
    labeledHexWalkEnd source czLiteralBlock0 = (source.1 + 3, source.2 + 3) := by
  rcases source with ⟨x, y⟩
  simp [czLiteralBlock0, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₀, labeledHexWalkEnd, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg] <;> omega

theorem czLiteralBlock5_walkEnd_power (source : HexVertex) (n : ℕ) :
    labeledHexWalkEnd source (labeledHexStepWordPower czLiteralBlock5 n) =
      walkPowerStart source (0, 3) n :=
  by
    rw [labeledHexStepWordPower_eq_labeledStepWordPower]
    exact labeledHexWalkEnd_power czLiteralBlock5 (0, 3) source
      (fun start => by simpa using czLiteralBlock5_walkEnd start) n

theorem czLiteralBlock4_walkEnd_power (source : HexVertex) (n : ℕ) :
    labeledHexWalkEnd source (labeledHexStepWordPower czLiteralBlock4 n) =
      walkPowerStart source (-3, 0) n :=
  by
    rw [labeledHexStepWordPower_eq_labeledStepWordPower]
    exact labeledHexWalkEnd_power czLiteralBlock4 (-3, 0) source
      (fun start => by simpa using czLiteralBlock4_walkEnd start) n

theorem czLiteralBlock3_walkEnd_power (source : HexVertex) (n : ℕ) :
    labeledHexWalkEnd source (labeledHexStepWordPower czLiteralBlock3 n) =
      walkPowerStart source (-3, -3) n :=
  by
    rw [labeledHexStepWordPower_eq_labeledStepWordPower]
    exact labeledHexWalkEnd_power czLiteralBlock3 (-3, -3) source
      (fun start => by simpa using czLiteralBlock3_walkEnd start) n

theorem czLiteralBlock2_walkEnd_power (source : HexVertex) (n : ℕ) :
    labeledHexWalkEnd source (labeledHexStepWordPower czLiteralBlock2 n) =
      walkPowerStart source (0, -3) n :=
  by
    rw [labeledHexStepWordPower_eq_labeledStepWordPower]
    exact labeledHexWalkEnd_power czLiteralBlock2 (0, -3) source
      (fun start => by simpa using czLiteralBlock2_walkEnd start) n

theorem czLiteralBlock1_walkEnd_power (source : HexVertex) (n : ℕ) :
    labeledHexWalkEnd source (labeledHexStepWordPower czLiteralBlock1 n) =
      walkPowerStart source (3, 0) n :=
  by
    rw [labeledHexStepWordPower_eq_labeledStepWordPower]
    exact labeledHexWalkEnd_power czLiteralBlock1 (3, 0) source
      (fun start => by simpa using czLiteralBlock1_walkEnd start) n

theorem czLiteralBlock0_walkEnd_power (source : HexVertex) (n : ℕ) :
    labeledHexWalkEnd source (labeledHexStepWordPower czLiteralBlock0 n) =
      walkPowerStart source (3, 3) n :=
  by
    rw [labeledHexStepWordPower_eq_labeledStepWordPower]
    exact labeledHexWalkEnd_power czLiteralBlock0 (3, 3) source
      (fun start => by simpa using czLiteralBlock0_walkEnd start) n

def czStage0 (s r : ℕ) : HexVertex := (2 * (s : ℤ) + r, (s : ℤ) - r)
def czStage1 (s r : ℕ) : HexVertex := (2 * (s : ℤ) + r, (s : ℤ) + 2 * r)
def czStage2 (s r : ℕ) : HexVertex := ((r : ℤ) - s, (s : ℤ) + 2 * r)
def czStage3 (s r : ℕ) : HexVertex := (-((s : ℤ)) - 2 * r, (s : ℤ) - r)
def czStage4 (s r : ℕ) : HexVertex := (-((s : ℤ)) - 2 * r, -2 * (s : ℤ) - r)
def czStage5 (s r : ℕ) : HexVertex := ((r : ℤ) - s, -2 * (s : ℤ) - r)

theorem czStage1_eq (s r : ℕ) :
    labeledHexWalkEnd (czStage0 s r)
      (labeledHexStepWordPower czLiteralBlock5 r) = czStage1 s r := by
  rw [czLiteralBlock5_walkEnd_power]
  apply Prod.ext <;> simp [czStage0, czStage1, walkPowerStart] <;> ring

theorem czStage2_eq (s r : ℕ) :
    labeledHexWalkEnd (czStage1 s r)
      (labeledHexStepWordPower czLiteralBlock4 s) = czStage2 s r := by
  rw [czLiteralBlock4_walkEnd_power]
  apply Prod.ext <;> simp [czStage1, czStage2, walkPowerStart] <;> ring

theorem czStage3_eq (s r : ℕ) :
    labeledHexWalkEnd (czStage2 s r)
      (labeledHexStepWordPower czLiteralBlock3 r) = czStage3 s r := by
  rw [czLiteralBlock3_walkEnd_power]
  apply Prod.ext <;> simp [czStage2, czStage3, walkPowerStart] <;> ring

theorem czStage4_eq (s r : ℕ) :
    labeledHexWalkEnd (czStage3 s r)
      (labeledHexStepWordPower czLiteralBlock2 s) = czStage4 s r := by
  rw [czLiteralBlock2_walkEnd_power]
  apply Prod.ext <;> simp [czStage3, czStage4, walkPowerStart] <;> ring

theorem czStage5_eq (s r : ℕ) :
    labeledHexWalkEnd (czStage4 s r)
      (labeledHexStepWordPower czLiteralBlock1 r) = czStage5 s r := by
  rw [czLiteralBlock1_walkEnd_power]
  apply Prod.ext <;> simp [czStage4, czStage5, walkPowerStart] <;> ring

theorem czStage6_eq (s r : ℕ) :
    labeledHexWalkEnd (czStage5 s r)
      (labeledHexStepWordPower czLiteralBlock0 s) = czStage0 s r := by
  rw [czLiteralBlock0_walkEnd_power]
  apply Prod.ext <;> simp [czStage5, czStage0, walkPowerStart] <;> ring

def classZeroBoundaryWalkBySegments (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (czStage0 s r) (labeledHexStepWordPower czLiteralBlock5 r) ++
  (walkLabeledHexEdges (czStage1 s r) (labeledHexStepWordPower czLiteralBlock4 s) ++
  (walkLabeledHexEdges (czStage2 s r) (labeledHexStepWordPower czLiteralBlock3 r) ++
  (walkLabeledHexEdges (czStage3 s r) (labeledHexStepWordPower czLiteralBlock2 s) ++
  (walkLabeledHexEdges (czStage4 s r) (labeledHexStepWordPower czLiteralBlock1 r) ++
    walkLabeledHexEdges (czStage5 s r) (labeledHexStepWordPower czLiteralBlock0 s)))))

theorem classZeroLiteralBoundaryWalk_eq_segments (s r : ℕ) :
    classZeroLiteralBoundaryWalk s r = classZeroBoundaryWalkBySegments s r := by
  rw [classZeroLiteralBoundaryWalk, classZeroLiteralBoundarySteps_eq_explicit]
  unfold classZeroLiteralBoundaryStepsExplicit classZeroBoundaryWalkBySegments
  change walkLabeledHexEdges (czStage0 s r) _ = _
  rw [walkLabeledHexEdges_append, czStage1_eq,
    walkLabeledHexEdges_append, czStage2_eq,
    walkLabeledHexEdges_append, czStage3_eq,
    walkLabeledHexEdges_append, czStage4_eq,
    walkLabeledHexEdges_append, czStage5_eq]

end FiniteDefects
