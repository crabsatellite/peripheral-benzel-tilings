import BenzelProblem6Kernel.ShadowWordAlgebra
import D4KernelOnly.D4ConwayLagariasTarget

/-!
# The class-minus-one shadow boundary on the d=4 diagonal

This is the literal specialization of the Kim--Propp class-minus-one shadow
word to `(a,b)=(m+4,2m+4)`, hence `s=1` and `t=m+1`.  The surrounding
Problem 6 package supplies only the already kernel-checked shadow-word
algebra.  No tiling invariant or stone-count theorem is imported here.
-/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4ShadowBlock0 : List ShadowStep :=
  [shadowB.neg, shadowA, shadowB.neg, shadowC]

def d4ShadowBlock1 : List ShadowStep :=
  [shadowA, shadowC.neg, shadowA, shadowB.neg]

def d4ShadowBlock2 : List ShadowStep :=
  [shadowA.neg, shadowC, shadowA.neg, shadowB]

def d4ShadowBlock3 : List ShadowStep :=
  [shadowC, shadowB.neg, shadowC, shadowA.neg]

def d4ShadowBlock4 : List ShadowStep :=
  [shadowC.neg, shadowB, shadowC.neg, shadowA]

def d4ShadowBlock5 : List ShadowStep :=
  [shadowB, shadowA.neg, shadowB, shadowC.neg]

def d4ClassMinusOneShadowWord (m : ℕ) : List ShadowStep :=
  shadowWordPower d4ShadowBlock0 1 ++ [shadowB.neg] ++
  shadowWordPower d4ShadowBlock1 (m + 1) ++ [shadowA] ++
  shadowWordPower d4ShadowBlock2 1 ++ [shadowA.neg] ++
  shadowWordPower d4ShadowBlock3 (m + 1) ++ [shadowC] ++
  shadowWordPower d4ShadowBlock4 1 ++ [shadowC.neg] ++
  shadowWordPower d4ShadowBlock5 (m + 1) ++ [shadowB]

theorem d4ShadowBlock0_summary :
    shadowWordSummary d4ShadowBlock0 = ⟨0, -3, -3⟩ := by
  decide

theorem d4ShadowBlock1_summary :
    shadowWordSummary d4ShadowBlock1 = ⟨3, 0, -3⟩ := by
  decide

theorem d4ShadowBlock2_summary :
    shadowWordSummary d4ShadowBlock2 = ⟨-3, 0, -3⟩ := by
  decide

theorem d4ShadowBlock3_summary :
    shadowWordSummary d4ShadowBlock3 = ⟨-3, -3, -3⟩ := by
  decide

theorem d4ShadowBlock4_summary :
    shadowWordSummary d4ShadowBlock4 = ⟨3, 3, -3⟩ := by
  decide

theorem d4ShadowBlock5_summary :
    shadowWordSummary d4ShadowBlock5 = ⟨0, 3, -3⟩ := by
  decide

theorem d4ClassMinusOneShadowWord_summary (m : ℕ) :
    shadowWordSummary (d4ClassMinusOneShadowWord m) =
      ⟨0, 0, -9 * ((m : ℤ) ^ 2 + (m : ℤ) + 2)⟩ := by
  simp only [d4ClassMinusOneShadowWord, shadowWordSummary_append,
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

def d4PositiveShadowWord (m : ℕ) : List ShadowStep :=
  (d4ClassMinusOneShadowWord m).reverse.map ShadowStep.neg

theorem d4PositiveShadowWord_summary (m : ℕ) :
    shadowWordSummary (d4PositiveShadowWord m) =
      ⟨0, 0, 9 * ((m : ℤ) ^ 2 + (m : ℤ) + 2)⟩ := by
  rw [d4PositiveShadowWord,
    shadowWordSummary_reverse_neg,
    d4ClassMinusOneShadowWord_summary]
  apply shadowSummary_ext <;> simp

theorem d4PositiveShadowWord_closed (m : ℕ) :
    (shadowWordSummary (d4PositiveShadowWord m)).x = 0 ∧
      (shadowWordSummary (d4PositiveShadowWord m)).y = 0 := by
  rw [d4PositiveShadowWord_summary]
  exact ⟨rfl, rfl⟩

theorem d4PositiveShadowWord_area_target (m : ℕ) :
    (shadowWordSummary (d4PositiveShadowWord m)).areaNumerator =
      18 * (d4KernelStoneTarget m : ℤ) := by
  rw [d4PositiveShadowWord_summary]
  have heven : 2 ∣ m * m + m + 2 :=
    two_dvd_d4KernelStoneTargetNumerator m
  have htwice := twice_d4KernelStoneTarget m
  push_cast at htwice ⊢
  nlinarith

end FiniteDefects
