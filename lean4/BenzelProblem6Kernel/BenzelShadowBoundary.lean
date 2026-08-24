import BenzelProblem6Kernel.CoxeterShadow

/-!
# Development of the peripheral benzel boundary

The six label blocks are the class-zero benzel boundary word.  The initial
rotation `benzelShadowFrame` is the convention in which its developed path is
the class-zero shadow word certified in `ClassZeroShadowWord`.
-/

namespace BenzelProblem6Kernel

def shadowLabelWordPower (word : List ShadowLabel) : ℕ → List ShadowLabel
  | 0 => []
  | exponent + 1 => shadowLabelWordPower word exponent ++ word

@[simp] theorem shadowLabelWordPower_zero (word : List ShadowLabel) :
    shadowLabelWordPower word 0 = [] := rfl

@[simp] theorem shadowLabelWordPower_succ
    (word : List ShadowLabel) (exponent : ℕ) :
    shadowLabelWordPower word (exponent + 1) =
      shadowLabelWordPower word exponent ++ word := rfl

theorem developFinalFrame_labelPower (frame : ShadowFrame)
    (word : List ShadowLabel)
    (hframe : developFinalFrame frame word = frame) (exponent : ℕ) :
    developFinalFrame frame (shadowLabelWordPower word exponent) = frame := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [shadowLabelWordPower_succ, developFinalFrame_append, ih, hframe]

theorem developShadowSteps_labelPower (frame : ShadowFrame)
    (word : List ShadowLabel)
    (hframe : developFinalFrame frame word = frame) (exponent : ℕ) :
    developShadowSteps frame (shadowLabelWordPower word exponent) =
      shadowWordPower (developShadowSteps frame word) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [shadowLabelWordPower_succ, developShadowSteps_append,
        developFinalFrame_labelPower frame word hframe exponent,
        shadowWordPower_succ, ih]

def classZeroBoundaryBlock₀ : List ShadowLabel := [.b, .a, .b, .c]
def classZeroBoundaryBlock₁ : List ShadowLabel := [.c, .a, .b, .a]
def classZeroBoundaryBlock₂ : List ShadowLabel := [.c, .b, .c, .a]
def classZeroBoundaryBlock₃ : List ShadowLabel := [.a, .b, .c, .b]
def classZeroBoundaryBlock₄ : List ShadowLabel := [.a, .c, .a, .b]
def classZeroBoundaryBlock₅ : List ShadowLabel := [.b, .c, .a, .c]

def classZeroBoundaryLabels (s t : ℕ) : List ShadowLabel :=
  shadowLabelWordPower classZeroBoundaryBlock₀ s ++
  shadowLabelWordPower classZeroBoundaryBlock₁ t ++
  shadowLabelWordPower classZeroBoundaryBlock₂ s ++
  shadowLabelWordPower classZeroBoundaryBlock₃ t ++
  shadowLabelWordPower classZeroBoundaryBlock₄ s ++
  shadowLabelWordPower classZeroBoundaryBlock₅ t

def benzelShadowFrame : ShadowFrame := ⟨-1, 1, -1, 0⟩

theorem benzelShadowFrame_det : benzelShadowFrame.det = 1 := by
  decide

theorem classZeroBoundaryBlock₀_frame :
    developFinalFrame benzelShadowFrame classZeroBoundaryBlock₀ =
      benzelShadowFrame := by decide

theorem classZeroBoundaryBlock₁_frame :
    developFinalFrame benzelShadowFrame classZeroBoundaryBlock₁ =
      benzelShadowFrame := by decide

theorem classZeroBoundaryBlock₂_frame :
    developFinalFrame benzelShadowFrame classZeroBoundaryBlock₂ =
      benzelShadowFrame := by decide

theorem classZeroBoundaryBlock₃_frame :
    developFinalFrame benzelShadowFrame classZeroBoundaryBlock₃ =
      benzelShadowFrame := by decide

theorem classZeroBoundaryBlock₄_frame :
    developFinalFrame benzelShadowFrame classZeroBoundaryBlock₄ =
      benzelShadowFrame := by decide

theorem classZeroBoundaryBlock₅_frame :
    developFinalFrame benzelShadowFrame classZeroBoundaryBlock₅ =
      benzelShadowFrame := by decide

theorem classZeroBoundaryBlock₀_develops :
    developShadowSteps benzelShadowFrame classZeroBoundaryBlock₀ =
      classZeroShadowBlock₀ := by decide

theorem classZeroBoundaryBlock₁_develops :
    developShadowSteps benzelShadowFrame classZeroBoundaryBlock₁ =
      classZeroShadowBlock₁ := by decide

theorem classZeroBoundaryBlock₂_develops :
    developShadowSteps benzelShadowFrame classZeroBoundaryBlock₂ =
      classZeroShadowBlock₂ := by decide

theorem classZeroBoundaryBlock₃_develops :
    developShadowSteps benzelShadowFrame classZeroBoundaryBlock₃ =
      classZeroShadowBlock₃ := by decide

theorem classZeroBoundaryBlock₄_develops :
    developShadowSteps benzelShadowFrame classZeroBoundaryBlock₄ =
      classZeroShadowBlock₄ := by decide

theorem classZeroBoundaryBlock₅_develops :
    developShadowSteps benzelShadowFrame classZeroBoundaryBlock₅ =
      classZeroShadowBlock₅ := by decide

theorem classZeroBoundaryBlock₀_power_frame (exponent : ℕ) :
    developFinalFrame benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₀ exponent) =
      benzelShadowFrame :=
  developFinalFrame_labelPower _ _ classZeroBoundaryBlock₀_frame exponent

theorem classZeroBoundaryBlock₁_power_frame (exponent : ℕ) :
    developFinalFrame benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₁ exponent) =
      benzelShadowFrame :=
  developFinalFrame_labelPower _ _ classZeroBoundaryBlock₁_frame exponent

theorem classZeroBoundaryBlock₂_power_frame (exponent : ℕ) :
    developFinalFrame benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₂ exponent) =
      benzelShadowFrame :=
  developFinalFrame_labelPower _ _ classZeroBoundaryBlock₂_frame exponent

theorem classZeroBoundaryBlock₃_power_frame (exponent : ℕ) :
    developFinalFrame benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₃ exponent) =
      benzelShadowFrame :=
  developFinalFrame_labelPower _ _ classZeroBoundaryBlock₃_frame exponent

theorem classZeroBoundaryBlock₄_power_frame (exponent : ℕ) :
    developFinalFrame benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₄ exponent) =
      benzelShadowFrame :=
  developFinalFrame_labelPower _ _ classZeroBoundaryBlock₄_frame exponent

theorem classZeroBoundaryBlock₅_power_frame (exponent : ℕ) :
    developFinalFrame benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₅ exponent) =
      benzelShadowFrame :=
  developFinalFrame_labelPower _ _ classZeroBoundaryBlock₅_frame exponent

theorem classZeroBoundaryBlock₀_power_develops (exponent : ℕ) :
    developShadowSteps benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₀ exponent) =
      shadowWordPower classZeroShadowBlock₀ exponent := by
  rw [developShadowSteps_labelPower _ _ classZeroBoundaryBlock₀_frame,
    classZeroBoundaryBlock₀_develops]

theorem classZeroBoundaryBlock₁_power_develops (exponent : ℕ) :
    developShadowSteps benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₁ exponent) =
      shadowWordPower classZeroShadowBlock₁ exponent := by
  rw [developShadowSteps_labelPower _ _ classZeroBoundaryBlock₁_frame,
    classZeroBoundaryBlock₁_develops]

theorem classZeroBoundaryBlock₂_power_develops (exponent : ℕ) :
    developShadowSteps benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₂ exponent) =
      shadowWordPower classZeroShadowBlock₂ exponent := by
  rw [developShadowSteps_labelPower _ _ classZeroBoundaryBlock₂_frame,
    classZeroBoundaryBlock₂_develops]

theorem classZeroBoundaryBlock₃_power_develops (exponent : ℕ) :
    developShadowSteps benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₃ exponent) =
      shadowWordPower classZeroShadowBlock₃ exponent := by
  rw [developShadowSteps_labelPower _ _ classZeroBoundaryBlock₃_frame,
    classZeroBoundaryBlock₃_develops]

theorem classZeroBoundaryBlock₄_power_develops (exponent : ℕ) :
    developShadowSteps benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₄ exponent) =
      shadowWordPower classZeroShadowBlock₄ exponent := by
  rw [developShadowSteps_labelPower _ _ classZeroBoundaryBlock₄_frame,
    classZeroBoundaryBlock₄_develops]

theorem classZeroBoundaryBlock₅_power_develops (exponent : ℕ) :
    developShadowSteps benzelShadowFrame
        (shadowLabelWordPower classZeroBoundaryBlock₅ exponent) =
      shadowWordPower classZeroShadowBlock₅ exponent := by
  rw [developShadowSteps_labelPower _ _ classZeroBoundaryBlock₅_frame,
    classZeroBoundaryBlock₅_develops]

theorem classZeroBoundary_develops (s t : ℕ) :
    developShadowSteps benzelShadowFrame (classZeroBoundaryLabels s t) =
      classZeroShadowWord s t := by
  simp only [classZeroBoundaryLabels, classZeroShadowWord,
    developShadowSteps_append, developFinalFrame_append,
    classZeroBoundaryBlock₀_power_frame,
    classZeroBoundaryBlock₁_power_frame,
    classZeroBoundaryBlock₂_power_frame,
    classZeroBoundaryBlock₃_power_frame,
    classZeroBoundaryBlock₄_power_frame,
    classZeroBoundaryBlock₅_power_frame,
    classZeroBoundaryBlock₀_power_develops,
    classZeroBoundaryBlock₁_power_develops,
    classZeroBoundaryBlock₂_power_develops,
    classZeroBoundaryBlock₃_power_develops,
    classZeroBoundaryBlock₄_power_develops,
    classZeroBoundaryBlock₅_power_develops]

theorem peripheralBoundary_shadow_summary (m : ℕ) :
    shadowWordSummary
        (developShadowSteps benzelShadowFrame
          (classZeroBoundaryLabels 1 (m + 3))) =
      ⟨0, 0, 9 * (m : ℤ) * (m + 3)⟩ := by
  rw [classZeroBoundary_develops, peripheralShadowWord_summary]

theorem peripheralBoundary_shadow_area_target (m : ℕ) :
    (shadowWordSummary
        (developShadowSteps benzelShadowFrame
          (classZeroBoundaryLabels 1 (m + 3)))).areaNumerator =
      6 * (3 * (m * (m + 3) / 2 : ℕ) : ℤ) := by
  rw [classZeroBoundary_develops]
  exact peripheralShadowWord_area_target m

theorem peripheralBoundary_identityFrame_area (m : ℕ) :
    (shadowWordSummary
        (developShadowSteps ShadowFrame.identity
          (classZeroBoundaryLabels 1 (m + 3)))).areaNumerator =
      9 * (m : ℤ) * (m + 3) := by
  have hsteps :
      developShadowSteps benzelShadowFrame
          (classZeroBoundaryLabels 1 (m + 3)) =
        (developShadowSteps ShadowFrame.identity
          (classZeroBoundaryLabels 1 (m + 3))).map
            benzelShadowFrame.apply := by
    simpa using developShadowSteps_equivariant
      benzelShadowFrame ShadowFrame.identity
        (classZeroBoundaryLabels 1 (m + 3))
  have hsummary := congrArg shadowWordSummary hsteps
  rw [shadowWordSummary_map_frame, benzelShadowFrame_det, one_mul] at hsummary
  have htarget := peripheralBoundary_shadow_summary m
  rw [htarget] at hsummary
  exact congrArg ShadowSummary.areaNumerator hsummary.symm

end BenzelProblem6Kernel
