import BenzelProblem6Kernel.ShadowWordMirror

/-!
# The premise-free class-zero peripheral boundary identity

This file upgrades the previously computed area coordinate to the complete
closed affine-A2 shadow word.  It then transports that identity through the
literal-coordinate reflection and orientation reversal.
-/

namespace BenzelProblem6Kernel

theorem classZeroBoundaryBlock₀_identity_frame :
    developFinalFrame ShadowFrame.identity classZeroBoundaryBlock₀ =
      ShadowFrame.identity := by
  decide

theorem classZeroBoundaryBlock₁_identity_frame :
    developFinalFrame ShadowFrame.identity classZeroBoundaryBlock₁ =
      ShadowFrame.identity := by
  decide

theorem classZeroBoundaryBlock₂_identity_frame :
    developFinalFrame ShadowFrame.identity classZeroBoundaryBlock₂ =
      ShadowFrame.identity := by
  decide

theorem classZeroBoundaryBlock₃_identity_frame :
    developFinalFrame ShadowFrame.identity classZeroBoundaryBlock₃ =
      ShadowFrame.identity := by
  decide

theorem classZeroBoundaryBlock₄_identity_frame :
    developFinalFrame ShadowFrame.identity classZeroBoundaryBlock₄ =
      ShadowFrame.identity := by
  decide

theorem classZeroBoundaryBlock₅_identity_frame :
    developFinalFrame ShadowFrame.identity classZeroBoundaryBlock₅ =
      ShadowFrame.identity := by
  decide

theorem classZeroBoundaryBlock₀_power_identity_frame (exponent : ℕ) :
    developFinalFrame ShadowFrame.identity
        (shadowLabelWordPower classZeroBoundaryBlock₀ exponent) =
      ShadowFrame.identity :=
  developFinalFrame_labelPower _ _
    classZeroBoundaryBlock₀_identity_frame exponent

theorem classZeroBoundaryBlock₁_power_identity_frame (exponent : ℕ) :
    developFinalFrame ShadowFrame.identity
        (shadowLabelWordPower classZeroBoundaryBlock₁ exponent) =
      ShadowFrame.identity :=
  developFinalFrame_labelPower _ _
    classZeroBoundaryBlock₁_identity_frame exponent

theorem classZeroBoundaryBlock₂_power_identity_frame (exponent : ℕ) :
    developFinalFrame ShadowFrame.identity
        (shadowLabelWordPower classZeroBoundaryBlock₂ exponent) =
      ShadowFrame.identity :=
  developFinalFrame_labelPower _ _
    classZeroBoundaryBlock₂_identity_frame exponent

theorem classZeroBoundaryBlock₃_power_identity_frame (exponent : ℕ) :
    developFinalFrame ShadowFrame.identity
        (shadowLabelWordPower classZeroBoundaryBlock₃ exponent) =
      ShadowFrame.identity :=
  developFinalFrame_labelPower _ _
    classZeroBoundaryBlock₃_identity_frame exponent

theorem classZeroBoundaryBlock₄_power_identity_frame (exponent : ℕ) :
    developFinalFrame ShadowFrame.identity
        (shadowLabelWordPower classZeroBoundaryBlock₄ exponent) =
      ShadowFrame.identity :=
  developFinalFrame_labelPower _ _
    classZeroBoundaryBlock₄_identity_frame exponent

theorem classZeroBoundaryBlock₅_power_identity_frame (exponent : ℕ) :
    developFinalFrame ShadowFrame.identity
        (shadowLabelWordPower classZeroBoundaryBlock₅ exponent) =
      ShadowFrame.identity :=
  developFinalFrame_labelPower _ _
    classZeroBoundaryBlock₅_identity_frame exponent

theorem classZeroBoundary_finalFrame_identity (s t : ℕ) :
    developFinalFrame ShadowFrame.identity (classZeroBoundaryLabels s t) =
      ShadowFrame.identity := by
  simp only [classZeroBoundaryLabels, developFinalFrame_append,
    classZeroBoundaryBlock₀_power_identity_frame,
    classZeroBoundaryBlock₁_power_identity_frame,
    classZeroBoundaryBlock₂_power_identity_frame,
    classZeroBoundaryBlock₃_power_identity_frame,
    classZeroBoundaryBlock₄_power_identity_frame,
    classZeroBoundaryBlock₅_power_identity_frame]

theorem peripheralBoundary_identityFrame_summary (m : ℕ) :
    shadowWordSummary
        (developShadowSteps ShadowFrame.identity
          (classZeroBoundaryLabels 1 (m + 3))) =
      ⟨0, 0, 9 * (m : ℤ) * (m + 3)⟩ := by
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
  rw [shadowWordSummary_map_frame,
    peripheralBoundary_shadow_summary] at hsummary
  let identitySummary := shadowWordSummary
    (developShadowSteps ShadowFrame.identity
      (classZeroBoundaryLabels 1 (m + 3)))
  have hsummary' :
      (⟨0, 0, 9 * (m : ℤ) * (m + 3)⟩ : ShadowSummary) =
        ⟨(benzelShadowFrame.apply identitySummary.displacement).x,
          (benzelShadowFrame.apply identitySummary.displacement).y,
          benzelShadowFrame.det * identitySummary.areaNumerator⟩ := by
    simpa [identitySummary] using hsummary
  have hx := congrArg ShadowSummary.x hsummary'
  have hy := congrArg ShadowSummary.y hsummary'
  have ha := congrArg ShadowSummary.areaNumerator hsummary'
  simp [ShadowSummary.displacement, benzelShadowFrame,
    ShadowFrame.apply, ShadowFrame.det] at hx hy ha
  change identitySummary = ⟨0, 0, 9 * (m : ℤ) * (m + 3)⟩
  apply shadowSummary_ext <;> simp only
  · omega
  · omega
  · exact ha.symm

theorem classZeroPeripheralBoundary_identity (m : ℕ) :
    IdentityShadowWord (classZeroBoundaryLabels 1 (m + 3))
      (9 * (m : ℤ) * (m + 3)) := by
  exact ⟨classZeroBoundary_finalFrame_identity 1 (m + 3),
    peripheralBoundary_identityFrame_summary m⟩

def literalPeripheralBoundaryLabels (m : ℕ) : List ShadowLabel :=
  mirrorReverseShadowWord (classZeroBoundaryLabels 1 (m + 3))

theorem literalPeripheralBoundary_identity (m : ℕ) :
    IdentityShadowWord (literalPeripheralBoundaryLabels m)
      (9 * (m : ℤ) * (m + 3)) := by
  exact identityShadowWord_mirrorReverse
    (classZeroPeripheralBoundary_identity m)

end BenzelProblem6Kernel
