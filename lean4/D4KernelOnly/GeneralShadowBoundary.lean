import D4KernelOnly.D4ShadowSymmetry
import BenzelProblem6Kernel.PeripheralBoundaryIdentity

/-! # Parameterized class-zero and class-minus-one shadow boundaries -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 800000

theorem classZeroBoundary_identityFrame_summary (s r : ℕ) :
    shadowWordSummary
        (developShadowSteps ShadowFrame.identity
          (classZeroBoundaryLabels s r)) =
      ⟨0, 0,
        9 * (s : ℤ) ^ 2 - 18 * (s : ℤ) * (r : ℤ) +
          9 * (r : ℤ) ^ 2 - 9 * (s : ℤ) - 9 * (r : ℤ)⟩ := by
  have hsteps :
      developShadowSteps benzelShadowFrame (classZeroBoundaryLabels s r) =
        (developShadowSteps ShadowFrame.identity
          (classZeroBoundaryLabels s r)).map benzelShadowFrame.apply := by
    simpa using developShadowSteps_equivariant
      benzelShadowFrame ShadowFrame.identity (classZeroBoundaryLabels s r)
  have hsummary := congrArg shadowWordSummary hsteps
  rw [classZeroBoundary_develops, classZeroShadowWord_summary,
    shadowWordSummary_map_frame, benzelShadowFrame_det, one_mul] at hsummary
  cases hsource : shadowWordSummary
      (developShadowSteps ShadowFrame.identity
        (classZeroBoundaryLabels s r)) with
  | mk x y area =>
      rw [hsource] at hsummary
      apply shadowSummary_ext <;>
        simp [benzelShadowFrame, ShadowFrame.apply,
          ShadowSummary.displacement] at hsummary ⊢
      all_goals omega

def classMinusOneShadowWord (s r : ℕ) : List ShadowStep :=
  shadowWordPower d4ShadowBlock0 s ++ [shadowB.neg] ++
  shadowWordPower d4ShadowBlock1 r ++ [shadowA] ++
  shadowWordPower d4ShadowBlock2 s ++ [shadowA.neg] ++
  shadowWordPower d4ShadowBlock3 r ++ [shadowC] ++
  shadowWordPower d4ShadowBlock4 s ++ [shadowC.neg] ++
  shadowWordPower d4ShadowBlock5 r ++ [shadowB]

theorem classMinusOneShadowWord_summary (s r : ℕ) :
    shadowWordSummary (classMinusOneShadowWord s r) =
      ⟨0, 0,
        -9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
          (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))⟩ := by
  simp only [classMinusOneShadowWord, shadowWordSummary_append,
    shadowWordSummary_power, d4ShadowBlock0_summary,
    d4ShadowBlock1_summary, d4ShadowBlock2_summary,
    d4ShadowBlock3_summary, d4ShadowBlock4_summary,
    d4ShadowBlock5_summary, shadowWordSummary,
    ShadowSummary.empty, ShadowSummary.single, ShadowSummary.scale,
    ShadowSummary.append, ShadowSummary.displacement, shadowCross,
    ShadowStep.neg_x, ShadowStep.neg_y, shadowA, shadowB, shadowC]
  apply shadowSummary_ext
  all_goals push_cast
  all_goals ring

def classMinusOnePositiveShadowWord (s r : ℕ) : List ShadowStep :=
  (classMinusOneShadowWord s r).reverse.map ShadowStep.neg

theorem classMinusOnePositiveShadowWord_summary (s r : ℕ) :
    shadowWordSummary (classMinusOnePositiveShadowWord s r) =
      ⟨0, 0,
        9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
          (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))⟩ := by
  rw [classMinusOnePositiveShadowWord,
    shadowWordSummary_reverse_neg,
    classMinusOneShadowWord_summary]
  apply shadowSummary_ext <;> simp

def classMinusOneSourceBoundaryLabels (s r : ℕ) : List ShadowLabel :=
  shadowLabelWordPower d4BoundaryBlock0 s ++ [.a] ++
  shadowLabelWordPower d4BoundaryBlock1 r ++ [.b] ++
  shadowLabelWordPower d4BoundaryBlock2 s ++ [.b] ++
  shadowLabelWordPower d4BoundaryBlock3 r ++ [.c] ++
  shadowLabelWordPower d4BoundaryBlock4 s ++ [.c] ++
  shadowLabelWordPower d4BoundaryBlock5 r ++ [.a]

theorem classMinusOneSourceBoundary_finalFrame (s r : ℕ) :
    developFinalFrame d4BoundaryFrame0
        (classMinusOneSourceBoundaryLabels s r) = d4BoundaryFrame0 := by
  simp only [classMinusOneSourceBoundaryLabels, developFinalFrame_append,
    developFinalFrame_labelPower _ _ d4BoundaryBlock0_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock1_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock2_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock3_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock4_frame,
    developFinalFrame_labelPower _ _ d4BoundaryBlock5_frame,
    d4Separator0.2, d4Separator1.2, d4Separator2.2,
    d4Separator3.2, d4Separator4.2, d4Separator5.2]

theorem classMinusOneSourceBoundary_develops (s r : ℕ) :
    developShadowSteps d4BoundaryFrame0
        (classMinusOneSourceBoundaryLabels s r) =
      classMinusOneShadowWord s r := by
  simp only [classMinusOneSourceBoundaryLabels, classMinusOneShadowWord,
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

theorem classMinusOneSourceBoundary_identity_finalFrame (s r : ℕ) :
    developFinalFrame ShadowFrame.identity
        (classMinusOneSourceBoundaryLabels s r) = ShadowFrame.identity := by
  have hequiv := developFinalFrame_equivariant
    d4BoundaryFrame0 ShadowFrame.identity
      (classMinusOneSourceBoundaryLabels s r)
  rw [ShadowFrame.comp_identity,
    classMinusOneSourceBoundary_finalFrame] at hequiv
  have hleft := congrArg (d4BoundaryFrame0Inv.comp) hequiv
  rw [← ShadowFrame.comp_assoc, d4BoundaryFrame0Inv_left,
    ShadowFrame.identity_comp] at hleft
  exact hleft.symm

theorem classMinusOneSourceBoundary_identity_summary (s r : ℕ) :
    shadowWordSummary
        (developShadowSteps ShadowFrame.identity
          (classMinusOneSourceBoundaryLabels s r)) =
      ⟨0, 0,
        -9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
          (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))⟩ := by
  have hsteps :
      developShadowSteps d4BoundaryFrame0
          (classMinusOneSourceBoundaryLabels s r) =
        (developShadowSteps ShadowFrame.identity
          (classMinusOneSourceBoundaryLabels s r)).map
            d4BoundaryFrame0.apply := by
    simpa using developShadowSteps_equivariant
      d4BoundaryFrame0 ShadowFrame.identity
        (classMinusOneSourceBoundaryLabels s r)
  have hsummary := congrArg shadowWordSummary hsteps
  rw [classMinusOneSourceBoundary_develops,
    classMinusOneShadowWord_summary,
    shadowWordSummary_map_frame, d4BoundaryFrame0_det, one_mul] at hsummary
  cases hsource : shadowWordSummary
      (developShadowSteps ShadowFrame.identity
        (classMinusOneSourceBoundaryLabels s r)) with
  | mk x y area =>
      rw [hsource] at hsummary
      apply shadowSummary_ext <;>
        simp [d4BoundaryFrame0, ShadowFrame.apply,
          ShadowSummary.displacement] at hsummary ⊢
      all_goals omega

theorem classMinusOneSourceBoundary_identityWord (s r : ℕ) :
    IdentityShadowWord (classMinusOneSourceBoundaryLabels s r)
      (-9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
        (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))) :=
  ⟨classMinusOneSourceBoundary_identity_finalFrame s r,
    classMinusOneSourceBoundary_identity_summary s r⟩

def classMinusOneReflectedReversedBoundaryLabels (s r : ℕ) :
    List ShadowLabel :=
  ((classMinusOneSourceBoundaryLabels s r).map swapABShadowLabel).reverse

def classMinusOneLiteralBoundaryLabels (s r : ℕ) : List ShadowLabel :=
  rotateHeadToTail (classMinusOneReflectedReversedBoundaryLabels s r)

theorem classMinusOneReflectedReversedBoundary_identityWord (s r : ℕ) :
    IdentityShadowWord (classMinusOneReflectedReversedBoundaryLabels s r)
      (-9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
        (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))) := by
  unfold classMinusOneReflectedReversedBoundaryLabels
  have hswap := identityShadowWord_map_swapAB
    (classMinusOneSourceBoundary_identityWord s r)
  have hreverse := identityShadowWord_reverse hswap
  simpa using hreverse

theorem classMinusOneReflectedReversedBoundary_nonempty (s r : ℕ) :
    classMinusOneReflectedReversedBoundaryLabels s r ≠ [] := by
  simp [classMinusOneReflectedReversedBoundaryLabels,
    classMinusOneSourceBoundaryLabels, shadowLabelWordPower]

theorem classMinusOneLiteralBoundary_identityWord (s r : ℕ) :
    IdentityShadowWord (classMinusOneLiteralBoundaryLabels s r)
      (9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
        (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))) := by
  have hnonempty := classMinusOneReflectedReversedBoundary_nonempty s r
  obtain ⟨head, tail, hword⟩ := List.exists_cons_of_ne_nil hnonempty
  have hid := classMinusOneReflectedReversedBoundary_identityWord s r
  rw [hword] at hid
  unfold classMinusOneLiteralBoundaryLabels rotateHeadToTail
  rw [hword]
  simpa using identityShadowWord_rotate_cons head tail
    (-9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
      (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))) hid

def classMinusOnePositiveBoundaryLabels (s r : ℕ) : List ShadowLabel :=
  (classMinusOneSourceBoundaryLabels s r).reverse

theorem classMinusOnePositiveBoundary_develops (s r : ℕ) :
    developShadowSteps d4BoundaryFrame0
        (classMinusOnePositiveBoundaryLabels s r) =
      classMinusOnePositiveShadowWord s r := by
  unfold classMinusOnePositiveBoundaryLabels classMinusOnePositiveShadowWord
  rw [← classMinusOneSourceBoundary_finalFrame s r,
    developShadowSteps_reverse,
    classMinusOneSourceBoundary_develops]

theorem classMinusOnePositiveBoundary_identityFrame_summary (s r : ℕ) :
    shadowWordSummary
        (developShadowSteps ShadowFrame.identity
          (classMinusOnePositiveBoundaryLabels s r)) =
      ⟨0, 0,
        9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
          (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ))⟩ := by
  have hsteps :
      developShadowSteps d4BoundaryFrame0
          (classMinusOnePositiveBoundaryLabels s r) =
        (developShadowSteps ShadowFrame.identity
          (classMinusOnePositiveBoundaryLabels s r)).map
            d4BoundaryFrame0.apply := by
    simpa using developShadowSteps_equivariant
      d4BoundaryFrame0 ShadowFrame.identity
        (classMinusOnePositiveBoundaryLabels s r)
  have hsummary := congrArg shadowWordSummary hsteps
  rw [classMinusOnePositiveBoundary_develops,
    classMinusOnePositiveShadowWord_summary,
    shadowWordSummary_map_frame, d4BoundaryFrame0_det, one_mul] at hsummary
  cases hsource : shadowWordSummary
      (developShadowSteps ShadowFrame.identity
        (classMinusOnePositiveBoundaryLabels s r)) with
  | mk x y area =>
      rw [hsource] at hsummary
      apply shadowSummary_ext <;>
        simp [d4BoundaryFrame0, ShadowFrame.apply,
          ShadowSummary.displacement] at hsummary ⊢
      all_goals omega

end FiniteDefects
