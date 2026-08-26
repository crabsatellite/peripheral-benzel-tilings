import D4KernelOnly.D4ClassMinusOneShadow
import BenzelProblem6Kernel.BenzelShadowBoundary

/-!
# Development of the class-minus-one d=4 boundary word

The label word is the Kim--Propp class-minus-one benzel boundary with
`s=1` and `t=m+1`, including its three isolated spurs.  Reversing it matches
the orientation of the literal `(m+4,2m+4)` carrier used in this project.
-/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4BoundaryBlock0 : List ShadowLabel := [.a, .b, .c, .b]
def d4BoundaryBlock1 : List ShadowLabel := [.b, .a, .c, .a]
def d4BoundaryBlock2 : List ShadowLabel := [.b, .c, .a, .c]
def d4BoundaryBlock3 : List ShadowLabel := [.c, .b, .a, .b]
def d4BoundaryBlock4 : List ShadowLabel := [.c, .a, .b, .a]
def d4BoundaryBlock5 : List ShadowLabel := [.a, .c, .b, .c]

def d4SourceBoundaryLabels (m : ℕ) : List ShadowLabel :=
  shadowLabelWordPower d4BoundaryBlock0 1 ++ [.a] ++
  shadowLabelWordPower d4BoundaryBlock1 (m + 1) ++ [.b] ++
  shadowLabelWordPower d4BoundaryBlock2 1 ++ [.b] ++
  shadowLabelWordPower d4BoundaryBlock3 (m + 1) ++ [.c] ++
  shadowLabelWordPower d4BoundaryBlock4 1 ++ [.c] ++
  shadowLabelWordPower d4BoundaryBlock5 (m + 1) ++ [.a]

def d4BoundaryFrame0 : ShadowFrame := ⟨0, 1, -1, 1⟩
def d4BoundaryFrame1 : ShadowFrame := ⟨0, 1, 1, 0⟩
def d4BoundaryFrame2 : ShadowFrame := ⟨1, -1, 1, 0⟩
def d4BoundaryFrame4 : ShadowFrame := ⟨-1, 0, 0, -1⟩

theorem d4BoundaryFrame0_det : d4BoundaryFrame0.det = 1 := by
  decide

theorem d4BoundaryBlock0_frame :
    developFinalFrame d4BoundaryFrame0 d4BoundaryBlock0 =
      d4BoundaryFrame0 := by decide

theorem d4BoundaryBlock1_frame :
    developFinalFrame d4BoundaryFrame1 d4BoundaryBlock1 =
      d4BoundaryFrame1 := by decide

theorem d4BoundaryBlock2_frame :
    developFinalFrame d4BoundaryFrame2 d4BoundaryBlock2 =
      d4BoundaryFrame2 := by decide

theorem d4BoundaryBlock3_frame :
    developFinalFrame d4BoundaryFrame1 d4BoundaryBlock3 =
      d4BoundaryFrame1 := by decide

theorem d4BoundaryBlock4_frame :
    developFinalFrame d4BoundaryFrame4 d4BoundaryBlock4 =
      d4BoundaryFrame4 := by decide

theorem d4BoundaryBlock5_frame :
    developFinalFrame d4BoundaryFrame1 d4BoundaryBlock5 =
      d4BoundaryFrame1 := by decide

theorem d4BoundaryBlock0_develops :
    developShadowSteps d4BoundaryFrame0 d4BoundaryBlock0 =
      d4ShadowBlock0 := by decide

theorem d4BoundaryBlock1_develops :
    developShadowSteps d4BoundaryFrame1 d4BoundaryBlock1 =
      d4ShadowBlock1 := by decide

theorem d4BoundaryBlock2_develops :
    developShadowSteps d4BoundaryFrame2 d4BoundaryBlock2 =
      d4ShadowBlock2 := by decide

theorem d4BoundaryBlock3_develops :
    developShadowSteps d4BoundaryFrame1 d4BoundaryBlock3 =
      d4ShadowBlock3 := by decide

theorem d4BoundaryBlock4_develops :
    developShadowSteps d4BoundaryFrame4 d4BoundaryBlock4 =
      d4ShadowBlock4 := by decide

theorem d4BoundaryBlock5_develops :
    developShadowSteps d4BoundaryFrame1 d4BoundaryBlock5 =
      d4ShadowBlock5 := by decide

theorem d4Separator0 :
    developShadowSteps d4BoundaryFrame0 [.a] = [shadowB.neg] ∧
      developFinalFrame d4BoundaryFrame0 [.a] = d4BoundaryFrame1 := by
  decide

theorem d4Separator1 :
    developShadowSteps d4BoundaryFrame1 [.b] = [shadowA] ∧
      developFinalFrame d4BoundaryFrame1 [.b] = d4BoundaryFrame2 := by
  decide

theorem d4Separator2 :
    developShadowSteps d4BoundaryFrame2 [.b] = [shadowA.neg] ∧
      developFinalFrame d4BoundaryFrame2 [.b] = d4BoundaryFrame1 := by
  decide

theorem d4Separator3 :
    developShadowSteps d4BoundaryFrame1 [.c] = [shadowC] ∧
      developFinalFrame d4BoundaryFrame1 [.c] = d4BoundaryFrame4 := by
  decide

theorem d4Separator4 :
    developShadowSteps d4BoundaryFrame4 [.c] = [shadowC.neg] ∧
      developFinalFrame d4BoundaryFrame4 [.c] = d4BoundaryFrame1 := by
  decide

theorem d4Separator5 :
    developShadowSteps d4BoundaryFrame1 [.a] = [shadowB] ∧
      developFinalFrame d4BoundaryFrame1 [.a] = d4BoundaryFrame0 := by
  decide

theorem d4SourceBoundary_finalFrame (m : ℕ) :
    developFinalFrame d4BoundaryFrame0 (d4SourceBoundaryLabels m) =
      d4BoundaryFrame0 := by
  simp only [d4SourceBoundaryLabels, developFinalFrame_append,
    developFinalFrame_labelPower _ _ d4BoundaryBlock0_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock1_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock2_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock3_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock4_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock5_frame,
    d4Separator0.2, d4Separator1.2, d4Separator2.2,
    d4Separator3.2, d4Separator4.2, d4Separator5.2]

theorem d4SourceBoundary_develops (m : ℕ) :
    developShadowSteps d4BoundaryFrame0 (d4SourceBoundaryLabels m) =
      d4ClassMinusOneShadowWord m := by
  simp only [d4SourceBoundaryLabels, d4ClassMinusOneShadowWord,
    developShadowSteps_append, developFinalFrame_append,
    developFinalFrame_labelPower _ _ d4BoundaryBlock0_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock1_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock2_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock3_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock4_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock5_frame,
    developShadowSteps_labelPower _ _ d4BoundaryBlock0_frame,
    developShadowSteps_labelPower _ _ d4BoundaryBlock1_frame,
    developShadowSteps_labelPower _ _ d4BoundaryBlock2_frame,
    developShadowSteps_labelPower _ _ d4BoundaryBlock3_frame,
    developShadowSteps_labelPower _ _ d4BoundaryBlock4_frame,
    developShadowSteps_labelPower _ _ d4BoundaryBlock5_frame,
    d4BoundaryBlock0_develops, d4BoundaryBlock1_develops,
    d4BoundaryBlock2_develops, d4BoundaryBlock3_develops,
    d4BoundaryBlock4_develops, d4BoundaryBlock5_develops,
    d4Separator0.1, d4Separator0.2, d4Separator1.1, d4Separator1.2,
    d4Separator2.1, d4Separator2.2, d4Separator3.1, d4Separator3.2,
    d4Separator4.1, d4Separator4.2, d4Separator5.1]

def d4PositiveBoundaryLabels (m : ℕ) : List ShadowLabel :=
  (d4SourceBoundaryLabels m).reverse

theorem d4PositiveBoundary_develops (m : ℕ) :
    developShadowSteps d4BoundaryFrame0 (d4PositiveBoundaryLabels m) =
      d4PositiveShadowWord m := by
  unfold d4PositiveBoundaryLabels d4PositiveShadowWord
  rw [← d4SourceBoundary_finalFrame m,
    developShadowSteps_reverse,
    d4SourceBoundary_develops]

theorem d4PositiveBoundary_shadow_area (m : ℕ) :
    (shadowWordSummary
      (developShadowSteps d4BoundaryFrame0
        (d4PositiveBoundaryLabels m))).areaNumerator =
      18 * (d4KernelStoneTarget m : ℤ) := by
  rw [d4PositiveBoundary_develops]
  exact d4PositiveShadowWord_area_target m

theorem d4PositiveBoundary_identityFrame_area (m : ℕ) :
    (shadowWordSummary
      (developShadowSteps ShadowFrame.identity
        (d4PositiveBoundaryLabels m))).areaNumerator =
      18 * (d4KernelStoneTarget m : ℤ) := by
  have hsteps :
      developShadowSteps d4BoundaryFrame0
          (d4PositiveBoundaryLabels m) =
        (developShadowSteps ShadowFrame.identity
          (d4PositiveBoundaryLabels m)).map d4BoundaryFrame0.apply := by
    simpa using developShadowSteps_equivariant
      d4BoundaryFrame0 ShadowFrame.identity
        (d4PositiveBoundaryLabels m)
  have hsummary := congrArg shadowWordSummary hsteps
  rw [shadowWordSummary_map_frame, d4BoundaryFrame0_det, one_mul] at hsummary
  have htarget := d4PositiveBoundary_shadow_area m
  have harea := congrArg ShadowSummary.areaNumerator hsummary
  exact harea.symm.trans htarget

end FiniteDefects
