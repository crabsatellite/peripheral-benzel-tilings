import BenzelProblem6Kernel.BenzelShadowBoundary

/-!
# Closed shadow words and conjugation

Tile boundaries have identity affine-A2 motion.  Their shoelace numerator is
therefore central: an even path to another `L_0` basepoint, followed by the
tile boundary and the reverse path, preserves the tile's signed shadow area.
-/

namespace BenzelProblem6Kernel

def EvenShadowLabelWord (word : List ShadowLabel) : Prop :=
  ∃ halfLength : ℕ, word.length = 2 * halfLength

def IdentityShadowWord (word : List ShadowLabel) (areaNumerator : ℤ) : Prop :=
  developFinalFrame ShadowFrame.identity word = ShadowFrame.identity ∧
    shadowWordSummary (developShadowSteps ShadowFrame.identity word) =
      ⟨0, 0, areaNumerator⟩

theorem developFinalFrame_det_of_even (frame : ShadowFrame)
    (word : List ShadowLabel) (heven : EvenShadowLabelWord word) :
    (developFinalFrame frame word).det = frame.det := by
  obtain ⟨halfLength, hlength⟩ := heven
  rw [developFinalFrame_det, hlength]
  simp [pow_mul]

theorem identityShadowWord_from_frame
    (frame : ShadowFrame) {word : List ShadowLabel} {areaNumerator : ℤ}
    (hword : IdentityShadowWord word areaNumerator) :
    developFinalFrame frame word = frame ∧
      shadowWordSummary (developShadowSteps frame word) =
        ⟨0, 0, frame.det * areaNumerator⟩ := by
  constructor
  · have h := developFinalFrame_equivariant
      frame ShadowFrame.identity word
    simpa [hword.1] using h
  · have hsteps := developShadowSteps_equivariant
      frame ShadowFrame.identity word
    have hsummary := congrArg shadowWordSummary hsteps
    rw [shadowWordSummary_map_frame, hword.2] at hsummary
    simpa [ShadowSummary.displacement, ShadowFrame.apply] using hsummary

theorem identityShadowWord_append
    {left right : List ShadowLabel} {leftArea rightArea : ℤ}
    (hleft : IdentityShadowWord left leftArea)
    (hright : IdentityShadowWord right rightArea) :
    IdentityShadowWord (left ++ right) (leftArea + rightArea) := by
  constructor
  · rw [developFinalFrame_append, hleft.1, hright.1]
  · rw [developShadowSteps_append, hleft.1, shadowWordSummary_append,
      hleft.2, hright.2]
    simp [ShadowSummary.append, ShadowSummary.displacement, shadowCross]

def shadowConjugate (path tileBoundary : List ShadowLabel) :
    List ShadowLabel :=
  path ++ tileBoundary ++ path.reverse

theorem identityShadowWord_conjugate
    {tileBoundary : List ShadowLabel} {areaNumerator : ℤ}
    (htile : IdentityShadowWord tileBoundary areaNumerator)
    (path : List ShadowLabel) (hpath : EvenShadowLabelWord path) :
    IdentityShadowWord (shadowConjugate path tileBoundary) areaNumerator := by
  let frame := developFinalFrame ShadowFrame.identity path
  have hframeDet : frame.det = 1 := by
    simpa [frame] using
      developFinalFrame_det_of_even ShadowFrame.identity path hpath
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
      shadowWordSummary_append, htileFrom.2, hframeDet, one_mul,
      hinverse, shadowWordSummary_reverse_neg]
    cases hsummary : shadowWordSummary
        (developShadowSteps ShadowFrame.identity path) with
    | mk x y area =>
        simp only [hsummary, ShadowSummary.append,
          ShadowSummary.displacement, shadowCross]
        apply shadowSummary_ext <;> ring

theorem rightStoneBoundary_identity :
    IdentityShadowWord rightStoneBoundaryLabels 18 := by
  constructor
  · exact rightStoneBoundary_finalFrame
  · rw [rightStoneBoundary_develops, rightStoneShadowWord_summary]

theorem boneABoundary_identity :
    IdentityShadowWord boneABoundaryLabels 0 := by
  constructor
  · exact boneABoundary_finalFrame
  · rw [boneABoundary_develops, boneAShadowWord_summary]

theorem boneBBoundary_identity :
    IdentityShadowWord boneBBoundaryLabels 0 := by
  constructor
  · exact boneBBoundary_finalFrame
  · rw [boneBBoundary_develops, boneBShadowWord_summary]

theorem boneCBoundary_identity :
    IdentityShadowWord boneCBoundaryLabels 0 := by
  constructor
  · exact boneCBoundary_finalFrame
  · rw [boneCBoundary_develops, boneCShadowWord_summary]

end BenzelProblem6Kernel
