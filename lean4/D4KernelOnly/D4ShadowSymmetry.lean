import D4KernelOnly.D4ClassMinusOneBoundary
import BenzelProblem6Kernel.ShadowWordMirror

/-!
# Reflection, reversal, and the class-zero d=4 boundary basepoint

The literal `(i,j)` carrier is obtained from the Kim--Propp boundary convention
by interchanging the `a` and `b` axes.  Reflection and orientation reversal
preserve the boundary invariant together; moving the basepoint across one
edge changes from the `L₁` to the `L₀` vertex class and reverses the sign once
more.
-/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4BoundaryFrame0Inv : ShadowFrame := ⟨1, -1, 1, 0⟩

theorem d4BoundaryFrame0Inv_left :
    d4BoundaryFrame0Inv.comp d4BoundaryFrame0 =
      ShadowFrame.identity := by decide

theorem d4SourceBoundary_identity_finalFrame (m : ℕ) :
    developFinalFrame ShadowFrame.identity (d4SourceBoundaryLabels m) =
      ShadowFrame.identity := by
  have hequiv := developFinalFrame_equivariant
    d4BoundaryFrame0 ShadowFrame.identity (d4SourceBoundaryLabels m)
  rw [ShadowFrame.comp_identity, d4SourceBoundary_finalFrame] at hequiv
  have hleft := congrArg (d4BoundaryFrame0Inv.comp) hequiv
  rw [← ShadowFrame.comp_assoc, d4BoundaryFrame0Inv_left,
    ShadowFrame.identity_comp] at hleft
  exact hleft.symm

theorem d4SourceBoundary_identity_summary (m : ℕ) :
    shadowWordSummary
      (developShadowSteps ShadowFrame.identity
        (d4SourceBoundaryLabels m)) =
      ⟨0, 0, -18 * (d4KernelStoneTarget m : ℤ)⟩ := by
  have hsteps :
      developShadowSteps d4BoundaryFrame0
          (d4SourceBoundaryLabels m) =
        (developShadowSteps ShadowFrame.identity
          (d4SourceBoundaryLabels m)).map d4BoundaryFrame0.apply := by
    simpa using developShadowSteps_equivariant
      d4BoundaryFrame0 ShadowFrame.identity (d4SourceBoundaryLabels m)
  have hsummary := congrArg shadowWordSummary hsteps
  rw [d4SourceBoundary_develops, d4ClassMinusOneShadowWord_summary,
    shadowWordSummary_map_frame, d4BoundaryFrame0_det, one_mul] at hsummary
  have htwice := twice_d4KernelStoneTarget m
  cases hsource : shadowWordSummary
      (developShadowSteps ShadowFrame.identity
        (d4SourceBoundaryLabels m)) with
  | mk x y area =>
      rw [hsource] at hsummary
      apply shadowSummary_ext <;>
        simp [d4BoundaryFrame0, ShadowFrame.apply,
          ShadowSummary.displacement] at hsummary ⊢
      all_goals push_cast at htwice ⊢
      all_goals nlinarith

theorem d4SourceBoundary_identityWord (m : ℕ) :
    IdentityShadowWord (d4SourceBoundaryLabels m)
      (-18 * (d4KernelStoneTarget m : ℤ)) :=
  ⟨d4SourceBoundary_identity_finalFrame m,
    d4SourceBoundary_identity_summary m⟩

def swapABShadowLabel : ShadowLabel → ShadowLabel
  | .a => .b
  | .b => .a
  | .c => .c

def swapABShadowFrame : ShadowFrame := ⟨0, 1, 1, 0⟩

theorem swapABShadowFrame_det : swapABShadowFrame.det = -1 := by decide

theorem swapABShadowFrame_involutive :
    swapABShadowFrame.comp swapABShadowFrame =
      ShadowFrame.identity := by decide

theorem swapABShadowFrame_identity_conjugate :
    (swapABShadowFrame.comp ShadowFrame.identity).comp swapABShadowFrame =
      ShadowFrame.identity := by decide

theorem swapABShadowLabel_step (label : ShadowLabel) :
    shadowLabelStep (swapABShadowLabel label) =
      swapABShadowFrame.apply (shadowLabelStep label) := by
  cases label <;> decide

theorem swapABShadowLabel_reflection (label : ShadowLabel) :
    shadowReflection (swapABShadowLabel label) =
      (swapABShadowFrame.comp (shadowReflection label)).comp
        swapABShadowFrame := by
  cases label <;> decide

theorem swapABShadowFrame_update (frame : ShadowFrame)
    (label : ShadowLabel) :
    (((swapABShadowFrame.comp frame).comp swapABShadowFrame).comp
        (shadowReflection (swapABShadowLabel label))) =
      (swapABShadowFrame.comp
        (frame.comp (shadowReflection label))).comp swapABShadowFrame := by
  cases label <;> cases frame <;>
    apply shadowFrame_ext <;>
    simp [swapABShadowLabel, swapABShadowFrame,
      ShadowFrame.comp, shadowReflection] <;> ring

theorem swapABShadowFrame_head (frame : ShadowFrame)
    (label : ShadowLabel) :
    ((swapABShadowFrame.comp frame).comp swapABShadowFrame).apply
        (shadowLabelStep (swapABShadowLabel label)) =
      swapABShadowFrame.apply (frame.apply (shadowLabelStep label)) := by
  cases label <;> cases frame <;>
    apply shadowStep_ext <;>
    simp [swapABShadowLabel, swapABShadowFrame,
      ShadowFrame.comp, ShadowFrame.apply, shadowLabelStep,
      shadowA, shadowB, shadowC] <;> ring

theorem developFinalFrame_map_swapAB_from (frame : ShadowFrame)
    (word : List ShadowLabel) :
    developFinalFrame
        ((swapABShadowFrame.comp frame).comp swapABShadowFrame)
        (word.map swapABShadowLabel) =
      (swapABShadowFrame.comp (developFinalFrame frame word)).comp
        swapABShadowFrame := by
  induction word generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [List.map_cons, developFinalFrame]
      rw [swapABShadowFrame_update]
      exact ih (frame.comp (shadowReflection label))

theorem developFinalFrame_map_swapAB (word : List ShadowLabel) :
    developFinalFrame ShadowFrame.identity (word.map swapABShadowLabel) =
      (swapABShadowFrame.comp
        (developFinalFrame ShadowFrame.identity word)).comp
          swapABShadowFrame := by
  rw [← swapABShadowFrame_identity_conjugate]
  exact developFinalFrame_map_swapAB_from ShadowFrame.identity word

theorem developShadowSteps_map_swapAB_from (frame : ShadowFrame)
    (word : List ShadowLabel) :
    developShadowSteps
        ((swapABShadowFrame.comp frame).comp swapABShadowFrame)
        (word.map swapABShadowLabel) =
      (developShadowSteps frame word).map swapABShadowFrame.apply := by
  induction word generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [List.map_cons, developShadowSteps]
      congr 1
      · exact swapABShadowFrame_head frame label
      · rw [swapABShadowFrame_update]
        exact ih (frame.comp (shadowReflection label))

theorem developShadowSteps_map_swapAB (word : List ShadowLabel) :
    developShadowSteps ShadowFrame.identity (word.map swapABShadowLabel) =
      (developShadowSteps ShadowFrame.identity word).map
        swapABShadowFrame.apply := by
  rw [← swapABShadowFrame_identity_conjugate]
  exact developShadowSteps_map_swapAB_from ShadowFrame.identity word

theorem identityShadowWord_map_swapAB
    {word : List ShadowLabel} {areaNumerator : ℤ}
    (hword : IdentityShadowWord word areaNumerator) :
    IdentityShadowWord (word.map swapABShadowLabel) (-areaNumerator) := by
  constructor
  · rw [developFinalFrame_map_swapAB, hword.1]
    exact swapABShadowFrame_identity_conjugate
  · rw [developShadowSteps_map_swapAB,
      shadowWordSummary_map_frame, hword.2,
      swapABShadowFrame_det]
    simp [ShadowSummary.displacement, ShadowFrame.apply]

theorem identityShadowWord_conjugate_det
    {tileBoundary : List ShadowLabel} {areaNumerator : ℤ}
    (htile : IdentityShadowWord tileBoundary areaNumerator)
    (path : List ShadowLabel) :
    let frame := developFinalFrame ShadowFrame.identity path
    IdentityShadowWord (shadowConjugate path tileBoundary)
      (frame.det * areaNumerator) := by
  let frame := developFinalFrame ShadowFrame.identity path
  have htileFrom := identityShadowWord_from_frame frame htile
  have hinverse := developShadowSteps_reverse ShadowFrame.identity path
  have hfinalReverse := developFinalFrame_reverse ShadowFrame.identity path
  constructor
  · simp only [shadowConjugate, developFinalFrame_append]
    rw [show developFinalFrame ShadowFrame.identity path = frame by rfl,
      htileFrom.1]
    exact hfinalReverse
  · simp only [shadowConjugate, developShadowSteps_append,
      developFinalFrame_append]
    rw [show developFinalFrame ShadowFrame.identity path = frame by rfl,
      htileFrom.1, shadowWordSummary_append,
      shadowWordSummary_append, htileFrom.2,
      hinverse, shadowWordSummary_reverse_neg]
    cases hsummary : shadowWordSummary
        (developShadowSteps ShadowFrame.identity path) with
    | mk x y area =>
        simp only [hsummary, ShadowSummary.append,
          ShadowSummary.displacement, shadowCross]
        apply shadowSummary_ext <;> ring

theorem identityShadowWord_of_equivalent
    {left right : List ShadowLabel} {areaNumerator : ℤ}
    (hleft : IdentityShadowWord left areaNumerator)
    (hequiv : InvolutiveWordEquivalent left right) :
    IdentityShadowWord right areaNumerator := by
  constructor
  · exact (equivalent_preserves_finalFrame hequiv).symm.trans hleft.1
  · exact (equivalent_preserves_summary hequiv).symm.trans hleft.2

theorem identityShadowWord_rotate_cons
    (head : ShadowLabel) (tail : List ShadowLabel) (areaNumerator : ℤ)
    (hword : IdentityShadowWord (head :: tail) areaNumerator) :
    IdentityShadowWord (tail ++ [head]) (-areaNumerator) := by
  have hconjugate := identityShadowWord_conjugate_det hword [head]
  have hdet :
      (developFinalFrame ShadowFrame.identity [head]).det = -1 := by
    cases head <;> decide
  change IdentityShadowWord (shadowConjugate [head] (head :: tail))
    ((developFinalFrame ShadowFrame.identity [head]).det * areaNumerator)
      at hconjugate
  rw [hdet, neg_one_mul] at hconjugate
  have hequiv : InvolutiveWordEquivalent
      (shadowConjugate [head] (head :: tail)) (tail ++ [head]) := by
    have hcancel : InvolutionCancelStep
        ([head, head] ++ tail ++ [head]) (tail ++ [head]) := by
      simpa [insertShadowWord, duplicateLabelWord, List.append_assoc] using
        InvolutionCancelStep.cancel [] (tail ++ [head]) head
    apply Relation.EqvGen.rel
    simpa [shadowConjugate, List.append_assoc] using hcancel
  exact identityShadowWord_of_equivalent hconjugate hequiv

def d4ReflectedReversedBoundaryLabels (m : ℕ) : List ShadowLabel :=
  ((d4SourceBoundaryLabels m).map swapABShadowLabel).reverse

def rotateHeadToTail {α : Type*} : List α → List α
  | [] => []
  | head :: tail => tail ++ [head]

def d4LiteralBoundaryLabels (m : ℕ) : List ShadowLabel :=
  rotateHeadToTail (d4ReflectedReversedBoundaryLabels m)

theorem d4ReflectedReversedBoundary_identityWord (m : ℕ) :
    IdentityShadowWord (d4ReflectedReversedBoundaryLabels m)
      (-18 * (d4KernelStoneTarget m : ℤ)) := by
  unfold d4ReflectedReversedBoundaryLabels
  have hswap := identityShadowWord_map_swapAB
    (d4SourceBoundary_identityWord m)
  have hreverse := identityShadowWord_reverse hswap
  simpa using hreverse

theorem d4ReflectedReversedBoundary_nonempty (m : ℕ) :
    d4ReflectedReversedBoundaryLabels m ≠ [] := by
  simp [d4ReflectedReversedBoundaryLabels, d4SourceBoundaryLabels,
    shadowLabelWordPower]

theorem d4LiteralBoundary_identityWord (m : ℕ) :
    IdentityShadowWord (d4LiteralBoundaryLabels m)
      (18 * (d4KernelStoneTarget m : ℤ)) := by
  have hnonempty := d4ReflectedReversedBoundary_nonempty m
  obtain ⟨head, tail, hword⟩ :=
    List.exists_cons_of_ne_nil hnonempty
  have hid := d4ReflectedReversedBoundary_identityWord m
  rw [hword] at hid
  unfold d4LiteralBoundaryLabels rotateHeadToTail
  rw [hword]
  simpa using identityShadowWord_rotate_cons head tail
    (-18 * (d4KernelStoneTarget m : ℤ))
    hid

end FiniteDefects
