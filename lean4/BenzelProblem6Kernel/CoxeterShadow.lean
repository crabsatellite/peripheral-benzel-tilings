import BenzelProblem6Kernel.TileShadowWords

/-!
# The affine-A2 shadow development

The original honeycomb boundary records only the three involutory edge
labels.  Reinterpreting the same label word in the affine Coxeter group
`T_0` develops a path in the shadow honeycomb.  A frame is the integral
linear part of the current chamber isometry; crossing a labeled wall composes
the frame with the corresponding root reflection.
-/

namespace BenzelProblem6Kernel

inductive ShadowLabel
  | a
  | b
  | c
  deriving DecidableEq

def shadowLabelStep : ShadowLabel → ShadowStep
  | .a => shadowA
  | .b => shadowB
  | .c => shadowC

structure ShadowFrame where
  xx : ℤ
  xy : ℤ
  yx : ℤ
  yy : ℤ
  deriving DecidableEq

@[ext] theorem shadowFrame_ext (left right : ShadowFrame)
    (hxx : left.xx = right.xx) (hxy : left.xy = right.xy)
    (hyx : left.yx = right.yx) (hyy : left.yy = right.yy) :
    left = right := by
  cases left
  cases right
  simp_all

def ShadowFrame.apply (frame : ShadowFrame) (step : ShadowStep) : ShadowStep :=
  ⟨frame.xx * step.x + frame.xy * step.y,
    frame.yx * step.x + frame.yy * step.y⟩

def ShadowFrame.comp (left right : ShadowFrame) : ShadowFrame :=
  ⟨left.xx * right.xx + left.xy * right.yx,
    left.xx * right.xy + left.xy * right.yy,
    left.yx * right.xx + left.yy * right.yx,
    left.yx * right.xy + left.yy * right.yy⟩

def ShadowFrame.identity : ShadowFrame := ⟨1, 0, 0, 1⟩

def ShadowFrame.det (frame : ShadowFrame) : ℤ :=
  frame.xx * frame.yy - frame.xy * frame.yx

def shadowReflection : ShadowLabel → ShadowFrame
  | .a => ⟨-1, 1, 0, 1⟩
  | .b => ⟨1, 0, 1, -1⟩
  | .c => ⟨0, -1, -1, 0⟩

@[simp] theorem ShadowFrame.identity_apply (step : ShadowStep) :
    ShadowFrame.identity.apply step = step := by
  cases step
  simp [ShadowFrame.identity, ShadowFrame.apply]

@[simp] theorem ShadowFrame.identity_comp (frame : ShadowFrame) :
    ShadowFrame.identity.comp frame = frame := by
  cases frame
  simp [ShadowFrame.identity, ShadowFrame.comp]

@[simp] theorem ShadowFrame.comp_identity (frame : ShadowFrame) :
    frame.comp ShadowFrame.identity = frame := by
  cases frame
  simp [ShadowFrame.identity, ShadowFrame.comp]

theorem ShadowFrame.comp_apply (left right : ShadowFrame) (step : ShadowStep) :
    (left.comp right).apply step = left.apply (right.apply step) := by
  cases left
  cases right
  cases step
  apply shadowStep_ext <;> simp [ShadowFrame.comp, ShadowFrame.apply] <;> ring

theorem ShadowFrame.comp_assoc
    (first second third : ShadowFrame) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  cases first
  cases second
  cases third
  apply shadowFrame_ext <;> simp [ShadowFrame.comp] <;> ring

theorem ShadowFrame.apply_neg (frame : ShadowFrame) (step : ShadowStep) :
    frame.apply step.neg = (frame.apply step).neg := by
  cases frame
  cases step
  apply shadowStep_ext <;> simp [ShadowFrame.apply] <;> ring

theorem shadowReflection_labelStep (label : ShadowLabel) :
    (shadowReflection label).apply (shadowLabelStep label) =
      (shadowLabelStep label).neg := by
  cases label <;> decide

theorem shadowReflection_involutive (label : ShadowLabel) :
    (shadowReflection label).comp (shadowReflection label) =
      ShadowFrame.identity := by
  cases label <;> decide

theorem shadowReflection_det (label : ShadowLabel) :
    (shadowReflection label).det = -1 := by
  cases label <;> decide

theorem ShadowFrame.det_comp (left right : ShadowFrame) :
    (left.comp right).det = left.det * right.det := by
  cases left
  cases right
  simp [ShadowFrame.comp, ShadowFrame.det]
  ring

theorem shadowCross_frame (frame : ShadowFrame) (left right : ShadowStep) :
    shadowCross (frame.apply left) (frame.apply right) =
      frame.det * shadowCross left right := by
  cases frame
  cases left
  cases right
  simp [ShadowFrame.apply, ShadowFrame.det, shadowCross]
  ring

def developShadowSteps : ShadowFrame → List ShadowLabel → List ShadowStep
  | _frame, [] => []
  | frame, label :: rest =>
      frame.apply (shadowLabelStep label) ::
        developShadowSteps (frame.comp (shadowReflection label)) rest

def developFinalFrame : ShadowFrame → List ShadowLabel → ShadowFrame
  | frame, [] => frame
  | frame, label :: rest =>
      developFinalFrame (frame.comp (shadowReflection label)) rest

theorem developShadowSteps_append (frame : ShadowFrame)
    (left right : List ShadowLabel) :
    developShadowSteps frame (left ++ right) =
      developShadowSteps frame left ++
        developShadowSteps (developFinalFrame frame left) right := by
  induction left generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [List.cons_append, developShadowSteps, developFinalFrame,
        List.cons.injEq, true_and]
      exact ih (frame.comp (shadowReflection label))

theorem developFinalFrame_append (frame : ShadowFrame)
    (left right : List ShadowLabel) :
    developFinalFrame frame (left ++ right) =
      developFinalFrame (developFinalFrame frame left) right := by
  induction left generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [List.cons_append, developFinalFrame]
      exact ih (frame.comp (shadowReflection label))

theorem developFinalFrame_reverse (frame : ShadowFrame)
    (word : List ShadowLabel) :
    developFinalFrame (developFinalFrame frame word) word.reverse = frame := by
  induction word generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [developFinalFrame, List.reverse_cons,
        developFinalFrame_append]
      rw [ih]
      simpa [ShadowFrame.comp_assoc] using
        congrArg (ShadowFrame.comp frame) (shadowReflection_involutive label)

theorem developShadowSteps_reverse (frame : ShadowFrame)
    (word : List ShadowLabel) :
    developShadowSteps (developFinalFrame frame word) word.reverse =
      (developShadowSteps frame word).reverse.map ShadowStep.neg := by
  induction word generalizing frame with
  | nil => rfl
  | cons label rest ih =>
      simp only [developShadowSteps, developFinalFrame, List.reverse_cons,
        developShadowSteps_append, developFinalFrame_reverse, List.reverse_cons,
        List.map_append, List.map_singleton]
      rw [ih]
      congr 1
      rw [ShadowFrame.comp_apply, shadowReflection_labelStep,
        ShadowFrame.apply_neg]

theorem developFinalFrame_det (frame : ShadowFrame)
    (word : List ShadowLabel) :
    (developFinalFrame frame word).det =
      frame.det * (-1 : ℤ) ^ word.length := by
  induction word generalizing frame with
  | nil => simp [developFinalFrame]
  | cons label rest ih =>
      simp only [developFinalFrame, List.length_cons, pow_succ]
      rw [ih, ShadowFrame.det_comp, shadowReflection_det]
      ring

theorem developShadowSteps_equivariant
    (left right : ShadowFrame) (word : List ShadowLabel) :
    developShadowSteps (left.comp right) word =
      (developShadowSteps right word).map left.apply := by
  induction word generalizing right with
  | nil => rfl
  | cons label rest ih =>
      simp only [developShadowSteps, List.map_cons]
      rw [ShadowFrame.comp_apply]
      congr 1
      rw [ShadowFrame.comp_assoc]
      exact ih (right.comp (shadowReflection label))

theorem developFinalFrame_equivariant
    (left right : ShadowFrame) (word : List ShadowLabel) :
    developFinalFrame (left.comp right) word =
      left.comp (developFinalFrame right word) := by
  induction word generalizing right with
  | nil => rfl
  | cons label rest ih =>
      simp only [developFinalFrame]
      rw [ShadowFrame.comp_assoc, ih]

theorem shadowWordSummary_map_frame
    (frame : ShadowFrame) (word : List ShadowStep) :
    shadowWordSummary (word.map frame.apply) =
      ⟨(frame.apply (shadowWordSummary word).displacement).x,
        (frame.apply (shadowWordSummary word).displacement).y,
        frame.det * (shadowWordSummary word).areaNumerator⟩ := by
  induction word with
  | nil =>
      simp [shadowWordSummary, ShadowSummary.empty, ShadowSummary.displacement,
        ShadowFrame.apply]
  | cons step rest ih =>
      simp only [List.map_cons, shadowWordSummary, ih,
        ShadowSummary.single, ShadowSummary.append,
        ShadowSummary.displacement, shadowCross_frame]
      apply shadowSummary_ext <;>
        simp only [ShadowFrame.apply, ShadowFrame.det, shadowCross] <;>
        ring

def rightStoneBoundaryLabels : List ShadowLabel :=
  [.a, .b, .a, .c, .b, .c, .b, .a, .c, .a, .c, .b]

def boneABoundaryLabels : List ShadowLabel :=
  [.a, .b, .a, .b, .a, .c, .b, .a, .b, .a, .b, .a, .c, .b]

def boneBBoundaryLabels : List ShadowLabel :=
  [.a, .c, .a, .c, .a, .c, .b, .a, .c, .a, .c, .a, .c, .b]

def boneCBoundaryLabels : List ShadowLabel :=
  [.a, .c, .b, .c, .b, .c, .b, .a, .c, .b, .c, .b, .c, .b]

theorem rightStoneBoundary_develops :
    developShadowSteps ShadowFrame.identity rightStoneBoundaryLabels =
      rightStoneShadowWord := by
  decide

theorem boneABoundary_develops :
    developShadowSteps ShadowFrame.identity boneABoundaryLabels =
      boneAShadowWord := by
  decide

theorem boneBBoundary_develops :
    developShadowSteps ShadowFrame.identity boneBBoundaryLabels =
      boneBShadowWord := by
  decide

theorem boneCBoundary_develops :
    developShadowSteps ShadowFrame.identity boneCBoundaryLabels =
      boneCShadowWord := by
  decide

theorem rightStoneBoundary_finalFrame :
    developFinalFrame ShadowFrame.identity rightStoneBoundaryLabels =
      ShadowFrame.identity := by
  decide

theorem boneABoundary_finalFrame :
    developFinalFrame ShadowFrame.identity boneABoundaryLabels =
      ShadowFrame.identity := by
  decide

theorem boneBBoundary_finalFrame :
    developFinalFrame ShadowFrame.identity boneBBoundaryLabels =
      ShadowFrame.identity := by
  decide

theorem boneCBoundary_finalFrame :
    developFinalFrame ShadowFrame.identity boneCBoundaryLabels =
      ShadowFrame.identity := by
  decide

end BenzelProblem6Kernel
