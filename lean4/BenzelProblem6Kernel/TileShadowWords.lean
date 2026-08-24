import BenzelProblem6Kernel.ClassZeroShadowWord

/-!
# Representative shadow words for the four allowed tile classes

The words below use one fixed orientation of the unlabeled Cayley-graph
identification.  Their summaries record the local Conway--Lagarias values:
the right stone contributes unrescaled area three (shoelace numerator 18),
and every bone orientation contributes zero.
-/

namespace BenzelProblem6Kernel

def rightStoneShadowWord : List ShadowStep :=
  [shadowA, shadowC.neg, shadowB, shadowC.neg,
    shadowB, shadowA.neg, shadowC, shadowA.neg,
    shadowC, shadowB.neg, shadowA, shadowB.neg]

def boneAShadowWord : List ShadowStep :=
  [shadowA, shadowC.neg, shadowB, shadowA.neg,
    shadowC, shadowA.neg, shadowC, shadowA.neg,
    shadowB, shadowC.neg, shadowA, shadowB.neg,
    shadowA, shadowB.neg]

def boneBShadowWord : List ShadowStep :=
  [shadowA, shadowB.neg, shadowC, shadowA.neg,
    shadowB, shadowC.neg, shadowB, shadowC.neg,
    shadowB, shadowA.neg, shadowC, shadowB.neg,
    shadowA, shadowB.neg]

def boneCShadowWord : List ShadowStep :=
  [shadowA, shadowB.neg, shadowA, shadowC.neg,
    shadowB, shadowA.neg, shadowC, shadowA.neg,
    shadowC, shadowA.neg, shadowB, shadowC.neg,
    shadowA, shadowB.neg]

theorem rightStoneShadowWord_summary :
    shadowWordSummary rightStoneShadowWord = ⟨0, 0, 18⟩ := by
  decide

theorem boneAShadowWord_summary :
    shadowWordSummary boneAShadowWord = ⟨0, 0, 0⟩ := by
  decide

theorem boneBShadowWord_summary :
    shadowWordSummary boneBShadowWord = ⟨0, 0, 0⟩ := by
  decide

theorem boneCShadowWord_summary :
    shadowWordSummary boneCShadowWord = ⟨0, 0, 0⟩ := by
  decide

end BenzelProblem6Kernel
