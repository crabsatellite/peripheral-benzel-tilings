import BenzelProblem6Kernel.GlobalBoundaryCancellation

/-!
# Reflection and reversal of affine-A2 shadow words

The literal `(i,j)` convention is the reflection of the boundary convention
used for the six class-zero blocks.  Reflection exchanges labels `b` and `c`
and reverses shadow area; reversing the reflected boundary reverses area once
more.  Thus the reflected, oppositely oriented word has exactly the original
closed-word area.
-/

namespace BenzelProblem6Kernel

def mirrorShadowLabel : ShadowLabel → ShadowLabel
  | .a => .a
  | .b => .c
  | .c => .b

def mirrorShadowFrame : ShadowFrame := ⟨1, -1, 0, -1⟩

theorem mirrorShadowFrame_det : mirrorShadowFrame.det = -1 := by
  decide

theorem mirrorShadowFrame_involutive :
    mirrorShadowFrame.comp mirrorShadowFrame = ShadowFrame.identity := by
  decide

theorem mirrorShadowFrame_identity_conjugate :
    (mirrorShadowFrame.comp ShadowFrame.identity).comp mirrorShadowFrame =
      ShadowFrame.identity := by
  decide

theorem mirrorShadowLabel_step (label : ShadowLabel) :
    shadowLabelStep (mirrorShadowLabel label) =
      mirrorShadowFrame.apply (shadowLabelStep label) := by
  cases label <;> decide

theorem mirrorShadowLabel_reflection (label : ShadowLabel) :
    shadowReflection (mirrorShadowLabel label) =
      (mirrorShadowFrame.comp (shadowReflection label)).comp
        mirrorShadowFrame := by
  cases label <;> decide

theorem mirrorShadowFrame_update (frame : ShadowFrame)
    (label : ShadowLabel) :
    (((mirrorShadowFrame.comp frame).comp mirrorShadowFrame).comp
        (shadowReflection (mirrorShadowLabel label))) =
      (mirrorShadowFrame.comp
        (frame.comp (shadowReflection label))).comp mirrorShadowFrame := by
  cases label <;> cases frame <;>
    apply shadowFrame_ext <;>
    simp [mirrorShadowLabel, mirrorShadowFrame,
      ShadowFrame.comp, shadowReflection] <;> ring

theorem mirrorShadowFrame_head (frame : ShadowFrame)
    (label : ShadowLabel) :
    ((mirrorShadowFrame.comp frame).comp mirrorShadowFrame).apply
        (shadowLabelStep (mirrorShadowLabel label)) =
      mirrorShadowFrame.apply (frame.apply (shadowLabelStep label)) := by
  cases label <;> cases frame <;>
    apply shadowStep_ext <;>
    simp [mirrorShadowLabel, mirrorShadowFrame,
      ShadowFrame.comp, ShadowFrame.apply, shadowLabelStep,
      shadowA, shadowB, shadowC] <;> ring

theorem developFinalFrame_map_mirror_from (frame : ShadowFrame)
    (word : List ShadowLabel) :
    developFinalFrame
        ((mirrorShadowFrame.comp frame).comp mirrorShadowFrame)
        (word.map mirrorShadowLabel) =
      (mirrorShadowFrame.comp (developFinalFrame frame word)).comp
        mirrorShadowFrame := by
  induction word generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [List.map_cons, developFinalFrame]
      rw [mirrorShadowFrame_update]
      exact ih (frame.comp (shadowReflection label))

theorem developFinalFrame_map_mirror (word : List ShadowLabel) :
    developFinalFrame ShadowFrame.identity (word.map mirrorShadowLabel) =
      (mirrorShadowFrame.comp
        (developFinalFrame ShadowFrame.identity word)).comp
          mirrorShadowFrame := by
  rw [← mirrorShadowFrame_identity_conjugate]
  exact developFinalFrame_map_mirror_from ShadowFrame.identity word

theorem developShadowSteps_map_mirror_from (frame : ShadowFrame)
    (word : List ShadowLabel) :
    developShadowSteps
        ((mirrorShadowFrame.comp frame).comp mirrorShadowFrame)
        (word.map mirrorShadowLabel) =
      (developShadowSteps frame word).map mirrorShadowFrame.apply := by
  induction word generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [List.map_cons, developShadowSteps]
      congr 1
      · exact mirrorShadowFrame_head frame label
      · rw [mirrorShadowFrame_update]
        exact ih (frame.comp (shadowReflection label))

theorem developShadowSteps_map_mirror (word : List ShadowLabel) :
    developShadowSteps ShadowFrame.identity (word.map mirrorShadowLabel) =
      (developShadowSteps ShadowFrame.identity word).map
        mirrorShadowFrame.apply := by
  rw [← mirrorShadowFrame_identity_conjugate]
  exact developShadowSteps_map_mirror_from ShadowFrame.identity word

theorem identityShadowWord_map_mirror
    {word : List ShadowLabel} {areaNumerator : ℤ}
    (hword : IdentityShadowWord word areaNumerator) :
    IdentityShadowWord (word.map mirrorShadowLabel) (-areaNumerator) := by
  constructor
  · rw [developFinalFrame_map_mirror, hword.1]
    exact mirrorShadowFrame_identity_conjugate
  · rw [developShadowSteps_map_mirror,
      shadowWordSummary_map_frame, hword.2,
      mirrorShadowFrame_det]
    simp [ShadowSummary.displacement, ShadowFrame.apply]

theorem identityShadowWord_reverse
    {word : List ShadowLabel} {areaNumerator : ℤ}
    (hword : IdentityShadowWord word areaNumerator) :
    IdentityShadowWord word.reverse (-areaNumerator) := by
  constructor
  · simpa [hword.1] using
      developFinalFrame_reverse ShadowFrame.identity word
  · have hsteps := developShadowSteps_reverse ShadowFrame.identity word
    rw [hword.1] at hsteps
    rw [hsteps, shadowWordSummary_reverse_neg, hword.2]
    simp

def mirrorReverseShadowWord (word : List ShadowLabel) : List ShadowLabel :=
  (word.map mirrorShadowLabel).reverse

theorem identityShadowWord_mirrorReverse
    {word : List ShadowLabel} {areaNumerator : ℤ}
    (hword : IdentityShadowWord word areaNumerator) :
    IdentityShadowWord (mirrorReverseShadowWord word) areaNumerator := by
  exact neg_neg areaNumerator ▸
    identityShadowWord_reverse (identityShadowWord_map_mirror hword)

end BenzelProblem6Kernel
