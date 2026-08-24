import BenzelProblem6Kernel.PeripheralBoundarySpurReduction

/-!
# Composition laws for Conway--Lagarias factorizations

These are the algebraic consumers of the planar split in the original
Conway--Lagarias induction.  Once two subregion boundaries factor, their
concatenated boundary factors with the concatenated face list and exact
additive tile multiplicities.
-/

namespace BenzelProblem6Kernel

theorem involutionCancelStep_append_right
    {left right : List ShadowLabel}
    (hstep : InvolutionCancelStep left right)
    (suffix : List ShadowLabel) :
    InvolutionCancelStep (left ++ suffix) (right ++ suffix) := by
  cases hstep with
  | cancel before after label =>
      simpa [insertShadowWord, duplicateLabelWord,
        List.append_assoc] using
          InvolutionCancelStep.cancel before (after ++ suffix) label

theorem involutionCancelStep_append_left
    (context : List ShadowLabel) {left right : List ShadowLabel}
    (hstep : InvolutionCancelStep left right) :
    InvolutionCancelStep (context ++ left) (context ++ right) := by
  cases hstep with
  | cancel before after label =>
      simpa [insertShadowWord, duplicateLabelWord,
        List.append_assoc] using
          InvolutionCancelStep.cancel (context ++ before) after label

theorem involutiveWordEquivalent_append_right
    {left right : List ShadowLabel}
    (heq : InvolutiveWordEquivalent left right)
    (suffix : List ShadowLabel) :
    InvolutiveWordEquivalent (left ++ suffix) (right ++ suffix) := by
  induction heq with
  | rel _ _ h =>
      exact Relation.EqvGen.rel _ _
        (involutionCancelStep_append_right h suffix)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

theorem involutiveWordEquivalent_append_left
    (context : List ShadowLabel) {left right : List ShadowLabel}
    (heq : InvolutiveWordEquivalent left right) :
    InvolutiveWordEquivalent (context ++ left) (context ++ right) := by
  induction heq with
  | rel _ _ h =>
      exact Relation.EqvGen.rel _ _
        (involutionCancelStep_append_left context h)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

theorem involutiveWordEquivalent_append
    {left₀ right₀ left₁ right₁ : List ShadowLabel}
    (h₀ : InvolutiveWordEquivalent left₀ right₀)
    (h₁ : InvolutiveWordEquivalent left₁ right₁) :
    InvolutiveWordEquivalent (left₀ ++ left₁) (right₀ ++ right₁) := by
  exact Relation.EqvGen.trans _ _ _
    (involutiveWordEquivalent_append_right h₀ left₁)
    (involutiveWordEquivalent_append_left right₀ h₁)

theorem conwayLagariasFactorWord_append
    (left right : List ConwayLagariasWordFactor) :
    conwayLagariasFactorWord (left ++ right) =
      conwayLagariasFactorWord left ++ conwayLagariasFactorWord right := by
  induction left with
  | nil => rfl
  | cons factor rest ih =>
      simp only [List.cons_append, conwayLagariasFactorWord, ih,
        List.append_assoc]

theorem conwayLagariasFactorArea_append
    (left right : List ConwayLagariasWordFactor) :
    conwayLagariasFactorArea (left ++ right) =
      conwayLagariasFactorArea left + conwayLagariasFactorArea right := by
  induction left with
  | nil => simp [conwayLagariasFactorArea]
  | cons factor rest ih =>
      simp [conwayLagariasFactorArea, ih, add_assoc]

theorem factorProtoTileCount_append
    (left right : List ConwayLagariasWordFactor) (tile : ProtoTile) :
    factorProtoTileCount (left ++ right) tile =
      factorProtoTileCount left tile + factorProtoTileCount right tile := by
  induction left with
  | nil => simp [factorProtoTileCount]
  | cons factor rest ih =>
      simp [factorProtoTileCount, ih, add_assoc]

theorem hasConwayLagariasWordFactorization_append
    {boundaryLeft boundaryRight : List ShadowLabel}
    {factorsLeft factorsRight : List ConwayLagariasWordFactor}
    (hleft : HasConwayLagariasWordFactorization boundaryLeft factorsLeft)
    (hright : HasConwayLagariasWordFactorization boundaryRight factorsRight) :
    HasConwayLagariasWordFactorization (boundaryLeft ++ boundaryRight)
      (factorsLeft ++ factorsRight) := by
  rw [HasConwayLagariasWordFactorization,
    conwayLagariasFactorWord_append]
  exact involutiveWordEquivalent_append hleft hright

theorem hasConwayLagariasWordFactorization_of_boundary_eq
    {boundaryLeft boundaryRight : List ShadowLabel}
    {factors : List ConwayLagariasWordFactor}
    (hboundary : boundaryLeft = boundaryRight)
    (hfactor : HasConwayLagariasWordFactorization boundaryRight factors) :
    HasConwayLagariasWordFactorization boundaryLeft factors := by
  rw [hboundary]
  exact hfactor

end BenzelProblem6Kernel
