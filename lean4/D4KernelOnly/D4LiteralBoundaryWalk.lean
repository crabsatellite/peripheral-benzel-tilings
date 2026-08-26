import D4KernelOnly.D4ShadowSymmetry
import BenzelProblem6Kernel.LiteralPlacementBoundary
import BenzelProblem6Kernel.HoneycombEdgePathParity

/-!
# The physical class-zero boundary walk of the d=4 benzel

The source steps are the class-minus-one word of Kim--Propp.  We apply the
literal-coordinate reflection, reverse the orientation, and move the first
edge to the end so that the root is in the class-zero vertex sublattice.
-/

namespace FiniteDefects

open BenzelProblem6Kernel

abbrev D4LabeledStep := BenzelProblem6Kernel.LabeledHexStep

def d4SourceStepBlock0 : List D4LabeledStep :=
  [(shadowA.neg, .a), (shadowB, .b), (shadowC.neg, .c), (shadowB, .b)]

def d4SourceStepBlock1 : List D4LabeledStep :=
  [(shadowB, .b), (shadowA.neg, .a), (shadowC, .c), (shadowA.neg, .a)]

def d4SourceStepBlock2 : List D4LabeledStep :=
  [(shadowB.neg, .b), (shadowC, .c), (shadowA.neg, .a), (shadowC, .c)]

def d4SourceStepBlock3 : List D4LabeledStep :=
  [(shadowC, .c), (shadowB.neg, .b), (shadowA, .a), (shadowB.neg, .b)]

def d4SourceStepBlock4 : List D4LabeledStep :=
  [(shadowC.neg, .c), (shadowA, .a), (shadowB.neg, .b), (shadowA, .a)]

def d4SourceStepBlock5 : List D4LabeledStep :=
  [(shadowA, .a), (shadowC.neg, .c), (shadowB, .b), (shadowC.neg, .c)]

def labeledStepWordPower (word : List D4LabeledStep) : ℕ →
    List D4LabeledStep
  | 0 => []
  | exponent + 1 => labeledStepWordPower word exponent ++ word

@[simp] theorem labeledStepWordPower_zero (word : List D4LabeledStep) :
    labeledStepWordPower word 0 = [] := rfl

@[simp] theorem labeledStepWordPower_succ
    (word : List D4LabeledStep) (exponent : ℕ) :
    labeledStepWordPower word (exponent + 1) =
      labeledStepWordPower word exponent ++ word := rfl

theorem labeledStepWordPower_map_snd
    (word : List D4LabeledStep) (exponent : ℕ) :
    (labeledStepWordPower word exponent).map Prod.snd =
      shadowLabelWordPower (word.map Prod.snd) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, shadowLabelWordPower_succ,
        List.map_append, ih]

def d4SourceBoundarySteps (m : ℕ) : List D4LabeledStep :=
  labeledStepWordPower d4SourceStepBlock0 1 ++ [(shadowA.neg, .a)] ++
  labeledStepWordPower d4SourceStepBlock1 (m + 1) ++ [(shadowB, .b)] ++
  labeledStepWordPower d4SourceStepBlock2 1 ++ [(shadowB.neg, .b)] ++
  labeledStepWordPower d4SourceStepBlock3 (m + 1) ++ [(shadowC, .c)] ++
  labeledStepWordPower d4SourceStepBlock4 1 ++ [(shadowC.neg, .c)] ++
  labeledStepWordPower d4SourceStepBlock5 (m + 1) ++ [(shadowA, .a)]

theorem d4SourceBoundarySteps_labels (m : ℕ) :
    (d4SourceBoundarySteps m).map Prod.snd =
      d4SourceBoundaryLabels m := by
  simp only [d4SourceBoundarySteps, d4SourceBoundaryLabels,
    List.map_append, List.map_singleton, labeledStepWordPower_map_snd]
  simp [d4SourceStepBlock0, d4SourceStepBlock1,
    d4SourceStepBlock2, d4SourceStepBlock3,
    d4SourceStepBlock4, d4SourceStepBlock5,
    d4BoundaryBlock0, d4BoundaryBlock1, d4BoundaryBlock2,
    d4BoundaryBlock3, d4BoundaryBlock4, d4BoundaryBlock5]

def reflectD4LabeledStep (step : D4LabeledStep) : D4LabeledStep :=
  (swapABShadowFrame.apply step.1, swapABShadowLabel step.2)

def reverseD4LabeledStep (step : D4LabeledStep) : D4LabeledStep :=
  (step.1.neg, step.2)

def d4ReflectedReversedBoundarySteps (m : ℕ) : List D4LabeledStep :=
  ((d4SourceBoundarySteps m).map reflectD4LabeledStep).reverse.map
    reverseD4LabeledStep

def d4LiteralBoundarySteps (m : ℕ) : List D4LabeledStep :=
  rotateHeadToTail (d4ReflectedReversedBoundarySteps m)

theorem map_snd_rotateHeadToTail {α β : Type*}
    (f : α → β) (items : List α) :
    (rotateHeadToTail items).map f =
      rotateHeadToTail (items.map f) := by
  cases items with
  | nil => rfl
  | cons head tail => simp [rotateHeadToTail]

theorem d4ReflectedReversedBoundarySteps_labels (m : ℕ) :
    (d4ReflectedReversedBoundarySteps m).map Prod.snd =
      d4ReflectedReversedBoundaryLabels m := by
  have hsource := congrArg (List.map swapABShadowLabel)
    (d4SourceBoundarySteps_labels m)
  have hreverse := congrArg List.reverse hsource
  simpa [d4ReflectedReversedBoundarySteps,
    d4ReflectedReversedBoundaryLabels, reflectD4LabeledStep,
    reverseD4LabeledStep, List.map_reverse, List.map_map,
    Function.comp_def] using hreverse

theorem d4LiteralBoundarySteps_labels (m : ℕ) :
    (d4LiteralBoundarySteps m).map Prod.snd =
      d4LiteralBoundaryLabels m := by
  rw [d4LiteralBoundarySteps, d4LiteralBoundaryLabels,
    map_snd_rotateHeadToTail,
    d4ReflectedReversedBoundarySteps_labels]

def d4LiteralBoundaryRoot (m : ℕ) : HexVertex :=
  ((m : ℤ), 2 * (m : ℤ) + 3)

def d4LiteralBoundaryWalk (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4LiteralBoundaryRoot m)
    (d4LiteralBoundarySteps m)

theorem d4LiteralBoundaryWalk_labels (m : ℕ) :
    labeledEdgeWord (d4LiteralBoundaryWalk m) =
      d4LiteralBoundaryLabels m := by
  rw [d4LiteralBoundaryWalk, labeledEdgeWord_walk,
    d4LiteralBoundarySteps_labels]

theorem d4LiteralBoundaryRoot_classZero (m : ℕ) :
    hexVertexClassZero (d4LiteralBoundaryRoot m) = true := by
  simp [d4LiteralBoundaryRoot, hexVertexClassZero]
  omega

end FiniteDefects
