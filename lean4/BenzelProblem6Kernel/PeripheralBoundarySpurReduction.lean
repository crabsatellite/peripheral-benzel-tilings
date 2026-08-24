import BenzelProblem6Kernel.ReducedPeripheralBoundaryWord

/-!
# The three literal peripheral spur cancellations

The augmented six-block word contains exactly the three adjacent pairs
`bb`, `aa`, and `cc`.  Removing them gives the literal reduced geometric
boundary word.
-/

namespace BenzelProblem6Kernel

theorem shadowLabelWordPower_succ_front
    (word : List ShadowLabel) (exponent : ℕ) :
    shadowLabelWordPower word (exponent + 1) =
      word ++ shadowLabelWordPower word exponent := by
  induction exponent with
  | zero => simp [shadowLabelWordPower]
  | succ exponent ih =>
      calc
        shadowLabelWordPower word (exponent + 1 + 1) =
            shadowLabelWordPower word (exponent + 1) ++ word := rfl
        _ = (word ++ shadowLabelWordPower word exponent) ++ word := by
          rw [ih]
        _ = word ++ (shadowLabelWordPower word exponent ++ word) :=
          List.append_assoc _ _ _
        _ = word ++ shadowLabelWordPower word (exponent + 1) := rfl

theorem shadowLabelWordPower_one (word : List ShadowLabel) :
    shadowLabelWordPower word 1 = word := by
  rfl

theorem involutionCancelStep_reverse {left right : List ShadowLabel}
    (hstep : InvolutionCancelStep left right) :
    InvolutionCancelStep left.reverse right.reverse := by
  cases hstep with
  | cancel before after label =>
      simpa [insertShadowWord, duplicateLabelWord,
        List.reverse_append, List.append_assoc] using
          InvolutionCancelStep.cancel after.reverse before.reverse label

theorem involutiveWordEquivalent_reverse {left right : List ShadowLabel}
    (heq : InvolutiveWordEquivalent left right) :
    InvolutiveWordEquivalent left.reverse right.reverse := by
  induction heq with
  | rel _ _ h =>
      exact Relation.EqvGen.rel _ _ (involutionCancelStep_reverse h)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

def peripheralSegment₁ (m : ℕ) : List ShadowLabel :=
  [.a, .c, .a] ++
    shadowLabelWordPower [.b, .a, .c, .a] (m + 2) ++
    [.b, .c, .b]

def peripheralSegment₃ (m : ℕ) : List ShadowLabel :=
  [.c, .b, .c] ++
    shadowLabelWordPower [.a, .c, .b, .c] (m + 2) ++
    [.a, .b, .a]

def peripheralSegment₅ (m : ℕ) : List ShadowLabel :=
  [.b, .a, .b] ++
    shadowLabelWordPower [.c, .b, .a, .b] (m + 2)

def literalPeripheralSpurWord (m : ℕ) : List ShadowLabel :=
  [.c, .a, .c] ++ [.b, .b] ++
    peripheralSegment₁ m ++ [.a, .a] ++
    peripheralSegment₃ m ++ [.c, .c] ++
    peripheralSegment₅ m

def literalPeripheralAfterB (m : ℕ) : List ShadowLabel :=
  [.c, .a, .c] ++ peripheralSegment₁ m ++ [.a, .a] ++
    peripheralSegment₃ m ++ [.c, .c] ++ peripheralSegment₅ m

def literalPeripheralAfterA (m : ℕ) : List ShadowLabel :=
  [.c, .a, .c] ++ peripheralSegment₁ m ++
    peripheralSegment₃ m ++ [.c, .c] ++ peripheralSegment₅ m

theorem mappedClassZeroBoundary_eq_spurWord (m : ℕ) :
    (classZeroBoundaryLabels 1 (m + 3)).map mirrorShadowLabel =
      literalPeripheralSpurWord m := by
  simp only [classZeroBoundaryLabels, List.map_append,
    shadowLabelWordPower_map_mirror, classZeroBoundaryBlock₀,
    classZeroBoundaryBlock₁, classZeroBoundaryBlock₂,
    classZeroBoundaryBlock₃, classZeroBoundaryBlock₄,
    classZeroBoundaryBlock₅, mirrorShadowLabel,
    shadowLabelWordPower_one]
  have h₁ : shadowLabelWordPower
      [ShadowLabel.c, ShadowLabel.a, ShadowLabel.b, ShadowLabel.a] (m + 3) =
        [ShadowLabel.c, ShadowLabel.a, ShadowLabel.b, ShadowLabel.a] ++
          shadowLabelWordPower
            [ShadowLabel.c, ShadowLabel.a, ShadowLabel.b, ShadowLabel.a]
            (m + 2) := by
    convert shadowLabelWordPower_succ_front
      [ShadowLabel.c, ShadowLabel.a, ShadowLabel.b, ShadowLabel.a] (m + 2) using 1
  have h₃ : shadowLabelWordPower
      [ShadowLabel.a, ShadowLabel.b, ShadowLabel.c, ShadowLabel.b] (m + 3) =
        [ShadowLabel.a, ShadowLabel.b, ShadowLabel.c, ShadowLabel.b] ++
          shadowLabelWordPower
            [ShadowLabel.a, ShadowLabel.b, ShadowLabel.c, ShadowLabel.b]
            (m + 2) := by
    convert shadowLabelWordPower_succ_front
      [ShadowLabel.a, ShadowLabel.b, ShadowLabel.c, ShadowLabel.b] (m + 2) using 1
  have h₅ : shadowLabelWordPower
      [ShadowLabel.b, ShadowLabel.c, ShadowLabel.a, ShadowLabel.c] (m + 3) =
        [ShadowLabel.b, ShadowLabel.c, ShadowLabel.a, ShadowLabel.c] ++
          shadowLabelWordPower
            [ShadowLabel.b, ShadowLabel.c, ShadowLabel.a, ShadowLabel.c]
            (m + 2) := by
    convert shadowLabelWordPower_succ_front
      [ShadowLabel.b, ShadowLabel.c, ShadowLabel.a, ShadowLabel.c] (m + 2) using 1
  rw [h₁, h₃, h₅]
  simp only [List.map_append]
  rw [← shadowLabelWordPower_map_mirror
      [ShadowLabel.c, ShadowLabel.a, ShadowLabel.b, ShadowLabel.a] (m + 2),
    ← shadowLabelWordPower_map_mirror
      [ShadowLabel.a, ShadowLabel.b, ShadowLabel.c, ShadowLabel.b] (m + 2),
    ← shadowLabelWordPower_map_mirror
      [ShadowLabel.b, ShadowLabel.c, ShadowLabel.a, ShadowLabel.c] (m + 2)]
  simp [literalPeripheralSpurWord, peripheralSegment₁,
    peripheralSegment₃, peripheralSegment₅, mirrorShadowLabel,
    List.append_assoc]

theorem reducedClockwiseLabels_eq_segments (m : ℕ) :
    literalReducedPeripheralClockwiseLabels m =
      [.c, .a, .c] ++ peripheralSegment₁ m ++
        peripheralSegment₃ m ++ peripheralSegment₅ m := by
  simp [literalReducedPeripheralClockwiseLabels,
    peripheralSegment₁, peripheralSegment₃,
    peripheralSegment₅, List.append_assoc]

theorem literalPeripheralSpurWord_equivalent_reduced (m : ℕ) :
    InvolutiveWordEquivalent (literalPeripheralSpurWord m)
      (literalReducedPeripheralClockwiseLabels m) := by
  have hB : InvolutiveWordEquivalent (literalPeripheralSpurWord m)
      (literalPeripheralAfterB m) := by
    let after := peripheralSegment₁ m ++ [.a, .a] ++
      peripheralSegment₃ m ++ [.c, .c] ++ peripheralSegment₅ m
    have hleft : literalPeripheralSpurWord m =
        insertShadowWord [.c, .a, .c] (duplicateLabelWord .b) after := by
      simp [literalPeripheralSpurWord, after, insertShadowWord,
        duplicateLabelWord, List.append_assoc]
    have hright : literalPeripheralAfterB m = [.c, .a, .c] ++ after := by
      simp [literalPeripheralAfterB, after, List.append_assoc]
    rw [hleft, hright]
    exact Relation.EqvGen.rel _ _
      (InvolutionCancelStep.cancel [.c, .a, .c] after .b)
  have hA : InvolutiveWordEquivalent (literalPeripheralAfterB m)
      (literalPeripheralAfterA m) := by
    let before := [.c, .a, .c] ++ peripheralSegment₁ m
    let after := peripheralSegment₃ m ++ [.c, .c] ++ peripheralSegment₅ m
    have hleft : literalPeripheralAfterB m =
        insertShadowWord before (duplicateLabelWord .a) after := by
      simp [literalPeripheralAfterB, before, after, insertShadowWord,
        duplicateLabelWord, List.append_assoc]
    have hright : literalPeripheralAfterA m = before ++ after := by
      simp [literalPeripheralAfterA, before, after, List.append_assoc]
    rw [hleft, hright]
    exact Relation.EqvGen.rel _ _
      (InvolutionCancelStep.cancel before after .a)
  have hC : InvolutiveWordEquivalent (literalPeripheralAfterA m)
      (literalReducedPeripheralClockwiseLabels m) := by
    let before := [.c, .a, .c] ++ peripheralSegment₁ m ++
      peripheralSegment₃ m
    let after := peripheralSegment₅ m
    have hleft : literalPeripheralAfterA m =
        insertShadowWord before (duplicateLabelWord .c) after := by
      simp [literalPeripheralAfterA, before, after, insertShadowWord,
        duplicateLabelWord, List.append_assoc]
    have hright : literalReducedPeripheralClockwiseLabels m =
        before ++ after := by
      rw [reducedClockwiseLabels_eq_segments]
    rw [hleft, hright]
    exact Relation.EqvGen.rel _ _
      (InvolutionCancelStep.cancel before after .c)
  exact Relation.EqvGen.trans _ _ _ hB
    (Relation.EqvGen.trans _ _ _ hA hC)

theorem literalPeripheralBoundary_equivalent_reduced (m : ℕ) :
    InvolutiveWordEquivalent (literalPeripheralBoundaryLabels m)
      (labeledEdgeWord (literalReducedPeripheralBoundary m)) := by
  have hclockwise : InvolutiveWordEquivalent
      ((classZeroBoundaryLabels 1 (m + 3)).map mirrorShadowLabel)
      (literalReducedPeripheralClockwiseLabels m) := by
    rw [mappedClassZeroBoundary_eq_spurWord]
    exact literalPeripheralSpurWord_equivalent_reduced m
  have hreversed := involutiveWordEquivalent_reverse hclockwise
  simpa [literalPeripheralBoundaryLabels, mirrorReverseShadowWord,
    labeledEdgeWord_literalReducedPeripheralBoundary] using hreversed

end BenzelProblem6Kernel
