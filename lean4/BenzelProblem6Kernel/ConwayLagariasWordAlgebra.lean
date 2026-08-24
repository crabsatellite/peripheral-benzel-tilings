import BenzelProblem6Kernel.ShadowWordConjugation
import BenzelProblem6Kernel.LiteralTileCounts
import Mathlib.Logic.Relation

/-!
# Involutive boundary-word algebra for the Conway--Lagarias producer

Honeycomb edge labels are involutions.  This file proves that deleting an
adjacent repeated label preserves the complete developed shadow motion, then
packages even-basepoint conjugates of the four literal prototile boundaries.
The geometric layer supplies the standard boundary factorization in this
involutive word quotient.
-/

namespace BenzelProblem6Kernel

def insertShadowWord (before middle after : List ShadowLabel) :
    List ShadowLabel :=
  before ++ middle ++ after

theorem developFinalFrame_insert_identity
    {middle : List ShadowLabel} (hmiddle : IdentityShadowWord middle 0)
    (before after : List ShadowLabel) :
    developFinalFrame ShadowFrame.identity
        (insertShadowWord before middle after) =
      developFinalFrame ShadowFrame.identity (before ++ after) := by
  let frame := developFinalFrame ShadowFrame.identity before
  have hmiddleFrom := identityShadowWord_from_frame frame hmiddle
  simp only [insertShadowWord, developFinalFrame_append]
  rw [show developFinalFrame ShadowFrame.identity before = frame by rfl,
    hmiddleFrom.1]

theorem shadowWordSummary_insert_identity
    {middle : List ShadowLabel} (hmiddle : IdentityShadowWord middle 0)
    (before after : List ShadowLabel) :
    shadowWordSummary
        (developShadowSteps ShadowFrame.identity
          (insertShadowWord before middle after)) =
      shadowWordSummary
        (developShadowSteps ShadowFrame.identity (before ++ after)) := by
  let frame := developFinalFrame ShadowFrame.identity before
  have hmiddleFrom := identityShadowWord_from_frame frame hmiddle
  simp only [insertShadowWord, developShadowSteps_append,
    developFinalFrame_append, shadowWordSummary_append]
  rw [show developFinalFrame ShadowFrame.identity before = frame by rfl,
    hmiddleFrom.1, hmiddleFrom.2]
  cases hbefore : shadowWordSummary
      (developShadowSteps ShadowFrame.identity before) with
  | mk px py pa =>
      cases hafter : shadowWordSummary (developShadowSteps frame after) with
      | mk sx sy sa =>
          simp only [hbefore, hafter, ShadowSummary.append,
            ShadowSummary.displacement, shadowCross, mul_zero]
          apply shadowSummary_ext <;> ring

def duplicateLabelWord (label : ShadowLabel) : List ShadowLabel :=
  [label, label]

theorem duplicateLabelWord_identity (label : ShadowLabel) :
    IdentityShadowWord (duplicateLabelWord label) 0 := by
  cases label <;> constructor <;> decide

inductive InvolutionCancelStep :
    List ShadowLabel → List ShadowLabel → Prop
  | cancel (before after : List ShadowLabel) (label : ShadowLabel) :
      InvolutionCancelStep
        (insertShadowWord before (duplicateLabelWord label) after)
        (before ++ after)

def InvolutiveWordEquivalent :
    List ShadowLabel → List ShadowLabel → Prop :=
  Relation.EqvGen InvolutionCancelStep

theorem cancellation_preserves_finalFrame
    {left right : List ShadowLabel}
    (hstep : InvolutionCancelStep left right) :
    developFinalFrame ShadowFrame.identity left =
      developFinalFrame ShadowFrame.identity right := by
  cases hstep with
  | cancel before after label =>
      exact developFinalFrame_insert_identity
        (duplicateLabelWord_identity label) before after

theorem cancellation_preserves_summary
    {left right : List ShadowLabel}
    (hstep : InvolutionCancelStep left right) :
    shadowWordSummary (developShadowSteps ShadowFrame.identity left) =
      shadowWordSummary (developShadowSteps ShadowFrame.identity right) := by
  cases hstep with
  | cancel before after label =>
      exact shadowWordSummary_insert_identity
        (duplicateLabelWord_identity label) before after

theorem equivalent_preserves_finalFrame
    {left right : List ShadowLabel}
    (heq : InvolutiveWordEquivalent left right) :
    developFinalFrame ShadowFrame.identity left =
      developFinalFrame ShadowFrame.identity right := by
  induction heq with
  | rel _ _ h => exact cancellation_preserves_finalFrame h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₀ ih₁ => exact ih₀.trans ih₁

theorem equivalent_preserves_summary
    {left right : List ShadowLabel}
    (heq : InvolutiveWordEquivalent left right) :
    shadowWordSummary (developShadowSteps ShadowFrame.identity left) =
      shadowWordSummary (developShadowSteps ShadowFrame.identity right) := by
  induction heq with
  | rel _ _ h => exact cancellation_preserves_summary h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₀ ih₁ => exact ih₀.trans ih₁

def protoTileBoundaryLabels : ProtoTile → List ShadowLabel
  | .stone => rightStoneBoundaryLabels
  | .boneA => boneABoundaryLabels
  | .boneB => boneBBoundaryLabels
  | .boneC => boneCBoundaryLabels

def protoTileShadowArea : ProtoTile → ℤ
  | .stone => 18
  | .boneA => 0
  | .boneB => 0
  | .boneC => 0

theorem protoTileBoundary_identity (tile : ProtoTile) :
    IdentityShadowWord (protoTileBoundaryLabels tile)
      (protoTileShadowArea tile) := by
  cases tile
  · exact rightStoneBoundary_identity
  · exact boneABoundary_identity
  · exact boneBBoundary_identity
  · exact boneCBoundary_identity

structure ConwayLagariasWordFactor where
  tile : ProtoTile
  path : List ShadowLabel
  path_even : EvenShadowLabelWord path

def ConwayLagariasWordFactor.word (factor : ConwayLagariasWordFactor) :
    List ShadowLabel :=
  shadowConjugate factor.path (protoTileBoundaryLabels factor.tile)

def ConwayLagariasWordFactor.area (factor : ConwayLagariasWordFactor) : ℤ :=
  protoTileShadowArea factor.tile

theorem ConwayLagariasWordFactor.identity
    (factor : ConwayLagariasWordFactor) :
    IdentityShadowWord factor.word factor.area :=
  identityShadowWord_conjugate
    (protoTileBoundary_identity factor.tile) factor.path factor.path_even

def conwayLagariasFactorWord : List ConwayLagariasWordFactor →
    List ShadowLabel
  | [] => []
  | factor :: rest => factor.word ++ conwayLagariasFactorWord rest

def conwayLagariasFactorArea : List ConwayLagariasWordFactor → ℤ
  | [] => 0
  | factor :: rest => factor.area + conwayLagariasFactorArea rest

theorem conwayLagariasFactorWord_identity
    (factors : List ConwayLagariasWordFactor) :
    IdentityShadowWord (conwayLagariasFactorWord factors)
      (conwayLagariasFactorArea factors) := by
  induction factors with
  | nil =>
      constructor <;>
        simp [conwayLagariasFactorWord, conwayLagariasFactorArea,
          IdentityShadowWord, developFinalFrame, developShadowSteps,
          shadowWordSummary, ShadowSummary.empty]
  | cons factor rest ih =>
      exact identityShadowWord_append factor.identity ih

def HasConwayLagariasWordFactorization
    (boundary : List ShadowLabel)
    (factors : List ConwayLagariasWordFactor) : Prop :=
  InvolutiveWordEquivalent boundary (conwayLagariasFactorWord factors)

theorem boundary_identity_of_conwayLagarias_factorization
    {boundary : List ShadowLabel} {factors : List ConwayLagariasWordFactor}
    (hfactor : HasConwayLagariasWordFactorization boundary factors) :
    IdentityShadowWord boundary (conwayLagariasFactorArea factors) := by
  have hproduct := conwayLagariasFactorWord_identity factors
  constructor
  · exact (equivalent_preserves_finalFrame hfactor).trans hproduct.1
  · exact (equivalent_preserves_summary hfactor).trans hproduct.2

end BenzelProblem6Kernel
