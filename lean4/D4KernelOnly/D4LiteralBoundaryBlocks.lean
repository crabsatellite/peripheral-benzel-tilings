import D4KernelOnly.D4LiteralBoundaryClosed

/-! # Explicit block normal form of the literal d=4 boundary walk -/

namespace FiniteDefects

open BenzelProblem6Kernel

def transformD4BoundaryStep (step : D4LabeledStep) : D4LabeledStep :=
  reverseD4LabeledStep (reflectD4LabeledStep step)

def transformD4BoundaryWord (word : List D4LabeledStep) :
    List D4LabeledStep :=
  word.reverse.map transformD4BoundaryStep

theorem reverse_reflectD4BoundaryWord (word : List D4LabeledStep) :
    (word.map reflectD4LabeledStep).reverse.map reverseD4LabeledStep =
      transformD4BoundaryWord word := by
  simp [transformD4BoundaryWord, transformD4BoundaryStep,
    List.map_reverse, List.map_map, Function.comp_def]

theorem labeledStepWordPower_commute
    (word : List D4LabeledStep) (exponent : ℕ) :
    word ++ labeledStepWordPower word exponent =
      labeledStepWordPower word exponent ++ word := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, ← List.append_assoc, ih,
        List.append_assoc]

@[simp] theorem labeledStepWordPower_one (word : List D4LabeledStep) :
    labeledStepWordPower word 1 = word := by
  rw [show 1 = 0 + 1 by omega, labeledStepWordPower_succ,
    labeledStepWordPower_zero, List.nil_append]

theorem transformD4BoundaryWord_power
    (word : List D4LabeledStep) (exponent : ℕ) :
    transformD4BoundaryWord (labeledStepWordPower word exponent) =
      labeledStepWordPower (transformD4BoundaryWord word) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, transformD4BoundaryWord,
        List.reverse_append, List.map_append]
      change transformD4BoundaryWord word ++
        transformD4BoundaryWord (labeledStepWordPower word exponent) = _
      rw [ih, labeledStepWordPower_succ,
        labeledStepWordPower_commute]

def d4LiteralStepBlock0 : List D4LabeledStep :=
  [(shadowA.neg, .a), (shadowC, .c), (shadowA.neg, .a), (shadowB, .b)]

def d4LiteralStepBlock1 : List D4LabeledStep :=
  [(shadowB, .b), (shadowC.neg, .c), (shadowB, .b), (shadowA.neg, .a)]

def d4LiteralStepBlock2 : List D4LabeledStep :=
  [(shadowC.neg, .c), (shadowB, .b), (shadowC.neg, .c), (shadowA, .a)]

def d4LiteralStepBlock3 : List D4LabeledStep :=
  [(shadowA, .a), (shadowB.neg, .b), (shadowA, .a), (shadowC.neg, .c)]

def d4LiteralStepBlock4 : List D4LabeledStep :=
  [(shadowB.neg, .b), (shadowA, .a), (shadowB.neg, .b), (shadowC, .c)]

def d4LiteralStepBlock5 : List D4LabeledStep :=
  [(shadowC, .c), (shadowA.neg, .a), (shadowC, .c), (shadowB.neg, .b)]

theorem transformD4SourceBlock0 :
    transformD4BoundaryWord d4SourceStepBlock0 = d4LiteralStepBlock0 := by decide
theorem transformD4SourceBlock1 :
    transformD4BoundaryWord d4SourceStepBlock1 = d4LiteralStepBlock1 := by decide
theorem transformD4SourceBlock2 :
    transformD4BoundaryWord d4SourceStepBlock2 = d4LiteralStepBlock2 := by decide
theorem transformD4SourceBlock3 :
    transformD4BoundaryWord d4SourceStepBlock3 = d4LiteralStepBlock3 := by decide
theorem transformD4SourceBlock4 :
    transformD4BoundaryWord d4SourceStepBlock4 = d4LiteralStepBlock4 := by decide
theorem transformD4SourceBlock5 :
    transformD4BoundaryWord d4SourceStepBlock5 = d4LiteralStepBlock5 := by decide

theorem transformD4Separator0 :
    transformD4BoundaryWord [(shadowA.neg, .a)] = [(shadowB, .b)] := by decide
theorem transformD4Separator1 :
    transformD4BoundaryWord [(shadowB, .b)] = [(shadowA.neg, .a)] := by decide
theorem transformD4Separator2 :
    transformD4BoundaryWord [(shadowB.neg, .b)] = [(shadowA, .a)] := by decide
theorem transformD4Separator3 :
    transformD4BoundaryWord [(shadowC, .c)] = [(shadowC.neg, .c)] := by decide
theorem transformD4Separator4 :
    transformD4BoundaryWord [(shadowC.neg, .c)] = [(shadowC, .c)] := by decide
theorem transformD4Separator5 :
    transformD4BoundaryWord [(shadowA, .a)] = [(shadowB.neg, .b)] := by decide

def d4LiteralBoundaryStepsCore (m : ℕ) : List D4LabeledStep :=
  labeledStepWordPower d4LiteralStepBlock5 (m + 1) ++
  ([(shadowC, .c)] ++ (d4LiteralStepBlock4 ++ ([(shadowC.neg, .c)] ++
  (labeledStepWordPower d4LiteralStepBlock3 (m + 1) ++
  ([(shadowA, .a)] ++ (d4LiteralStepBlock2 ++ ([(shadowA.neg, .a)] ++
  (labeledStepWordPower d4LiteralStepBlock1 (m + 1) ++
  ([(shadowB, .b)] ++ d4LiteralStepBlock0)))))))))

def d4LiteralBoundaryStepsExplicit (m : ℕ) : List D4LabeledStep :=
  labeledStepWordPower d4LiteralStepBlock5 (m + 1) ++
  ([(shadowC, .c)] ++ (d4LiteralStepBlock4 ++ ([(shadowC.neg, .c)] ++
  (labeledStepWordPower d4LiteralStepBlock3 (m + 1) ++
  ([(shadowA, .a)] ++ (d4LiteralStepBlock2 ++ ([(shadowA.neg, .a)] ++
  (labeledStepWordPower d4LiteralStepBlock1 (m + 1) ++
  ([(shadowB, .b)] ++ (d4LiteralStepBlock0 ++ [(shadowB.neg, .b)]))))))))))

theorem d4ReflectedReversedBoundarySteps_eq_cons_core (m : ℕ) :
    d4ReflectedReversedBoundarySteps m =
      (shadowB.neg, .b) :: d4LiteralBoundaryStepsCore m := by
  simp only [d4ReflectedReversedBoundarySteps,
    d4SourceBoundarySteps, List.reverse_append, List.map_append,
    List.reverse_singleton, List.map_singleton,
    reverse_reflectD4BoundaryWord,
    transformD4BoundaryWord_power,
    transformD4SourceBlock0, transformD4SourceBlock1,
    transformD4SourceBlock2, transformD4SourceBlock3,
    transformD4SourceBlock4, transformD4SourceBlock5,
    transformD4Separator0, transformD4Separator1,
    transformD4Separator2, transformD4Separator3,
    transformD4Separator4, transformD4Separator5,
    d4LiteralBoundaryStepsCore]
  simp [reflectD4LabeledStep, reverseD4LabeledStep,
    swapABShadowFrame, swapABShadowLabel, ShadowFrame.apply,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem d4LiteralBoundarySteps_eq_explicit (m : ℕ) :
    d4LiteralBoundarySteps m = d4LiteralBoundaryStepsExplicit m := by
  simp only [d4LiteralBoundarySteps, rotateHeadToTail,
    d4LiteralBoundaryStepsExplicit, d4LiteralBoundaryStepsCore]
  rw [d4ReflectedReversedBoundarySteps_eq_cons_core]
  simp [rotateHeadToTail, d4LiteralBoundaryStepsCore]

end FiniteDefects
