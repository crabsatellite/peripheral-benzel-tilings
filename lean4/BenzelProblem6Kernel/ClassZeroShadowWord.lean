import BenzelProblem6Kernel.ShadowWordAlgebra

/-!
# The class-zero benzel shadow word

This is the six-block shadow word used for class-zero benzels.  At the
peripheral specialization `(a,b) = (m+5, 2m+7)`, its block exponents are
`s = 1` and `t = m+3`.
-/

namespace BenzelProblem6Kernel

def classZeroShadowBlock₀ : List ShadowStep :=
  [shadowA, shadowB.neg, shadowC, shadowB.neg]

def classZeroShadowBlock₁ : List ShadowStep :=
  [shadowB, shadowA.neg, shadowB, shadowC.neg]

def classZeroShadowBlock₂ : List ShadowStep :=
  [shadowB, shadowC.neg, shadowA, shadowC.neg]

def classZeroShadowBlock₃ : List ShadowStep :=
  [shadowC, shadowB.neg, shadowC, shadowA.neg]

def classZeroShadowBlock₄ : List ShadowStep :=
  [shadowC, shadowA.neg, shadowB, shadowA.neg]

def classZeroShadowBlock₅ : List ShadowStep :=
  [shadowA, shadowC.neg, shadowA, shadowB.neg]

def classZeroShadowWord (s t : ℕ) : List ShadowStep :=
  shadowWordPower classZeroShadowBlock₀ s ++
  shadowWordPower classZeroShadowBlock₁ t ++
  shadowWordPower classZeroShadowBlock₂ s ++
  shadowWordPower classZeroShadowBlock₃ t ++
  shadowWordPower classZeroShadowBlock₄ s ++
  shadowWordPower classZeroShadowBlock₅ t

theorem classZeroShadowBlock₀_summary :
    shadowWordSummary classZeroShadowBlock₀ = ⟨0, -3, -3⟩ := by
  decide

theorem classZeroShadowBlock₁_summary :
    shadowWordSummary classZeroShadowBlock₁ = ⟨0, 3, -3⟩ := by
  decide

theorem classZeroShadowBlock₂_summary :
    shadowWordSummary classZeroShadowBlock₂ = ⟨3, 3, -3⟩ := by
  decide

theorem classZeroShadowBlock₃_summary :
    shadowWordSummary classZeroShadowBlock₃ = ⟨-3, -3, -3⟩ := by
  decide

theorem classZeroShadowBlock₄_summary :
    shadowWordSummary classZeroShadowBlock₄ = ⟨-3, 0, -3⟩ := by
  decide

theorem classZeroShadowBlock₅_summary :
    shadowWordSummary classZeroShadowBlock₅ = ⟨3, 0, -3⟩ := by
  decide

theorem classZeroShadowWord_summary (s t : ℕ) :
    shadowWordSummary (classZeroShadowWord s t) =
      ⟨0, 0,
        9 * (s : ℤ) ^ 2 - 18 * (s : ℤ) * (t : ℤ) +
          9 * (t : ℤ) ^ 2 - 9 * (s : ℤ) - 9 * (t : ℤ)⟩ := by
  simp only [classZeroShadowWord, shadowWordSummary_append,
    shadowWordSummary_power, classZeroShadowBlock₀_summary,
    classZeroShadowBlock₁_summary, classZeroShadowBlock₂_summary,
    classZeroShadowBlock₃_summary, classZeroShadowBlock₄_summary,
    classZeroShadowBlock₅_summary, ShadowSummary.scale,
    ShadowSummary.append, ShadowSummary.displacement, shadowCross]
  apply shadowSummary_ext
  all_goals push_cast
  all_goals ring

theorem peripheralShadowWord_summary (m : ℕ) :
    shadowWordSummary (classZeroShadowWord 1 (m + 3)) =
      ⟨0, 0, 9 * (m : ℤ) * (m + 3)⟩ := by
  rw [classZeroShadowWord_summary]
  apply shadowSummary_ext
  all_goals push_cast
  all_goals ring

theorem peripheralShadowWord_closed (m : ℕ) :
    (shadowWordSummary (classZeroShadowWord 1 (m + 3))).x = 0 ∧
      (shadowWordSummary (classZeroShadowWord 1 (m + 3))).y = 0 := by
  rw [peripheralShadowWord_summary]
  exact ⟨rfl, rfl⟩

theorem peripheral_stone_product_even (m : ℕ) : 2 ∣ m * (m + 3) := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · refine ⟨k * (2 * k + 3), ?_⟩
    ring
  · refine ⟨(2 * k + 1) * (k + 2), ?_⟩
    ring

theorem peripheralShadowWord_area_target (m : ℕ) :
    (shadowWordSummary (classZeroShadowWord 1 (m + 3))).areaNumerator =
      6 * (3 * (m * (m + 3) / 2 : ℕ) : ℤ) := by
  rw [peripheralShadowWord_summary]
  have heven : 2 ∣ m * (m + 3) := peripheral_stone_product_even m
  obtain ⟨k, hk⟩ := heven
  have hdiv : m * (m + 3) / 2 = k := by omega
  rw [hdiv]
  have hkZ : (m : ℤ) * (m + 3) = 2 * (k : ℤ) := by
    exact_mod_cast hk
  push_cast
  calc
    9 * (m : ℤ) * ((m : ℤ) + 3) =
        9 * ((m : ℤ) * ((m : ℤ) + 3)) := by ring
    _ = 9 * (2 * (k : ℤ)) := by rw [hkZ]
    _ = 6 * (3 * (k : ℤ)) := by ring

end BenzelProblem6Kernel
