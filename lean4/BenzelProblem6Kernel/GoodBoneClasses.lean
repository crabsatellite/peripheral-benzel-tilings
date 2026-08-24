import BenzelProblem6Kernel.LiteralEnergyRigidity
import BenzelProblem6Kernel.LiteralBoneEdges
import BenzelProblem6Kernel.OwnerStepTransport

/-!
# The six literal two-owner bone classes
-/

namespace BenzelProblem6Kernel

inductive GoodBoneClass
  | boneA0
  | boneA2
  | boneB0
  | boneB1
  | boneC0
  | boneC2
  deriving DecidableEq, Repr

def GoodBoneClass.tile : GoodBoneClass → ProtoTile
  | .boneA0 | .boneA2 => .boneA
  | .boneB0 | .boneB1 => .boneB
  | .boneC0 | .boneC2 => .boneC

def GoodBoneClass.residue : GoodBoneClass → Res3
  | .boneA0 | .boneB0 | .boneC0 => .r0
  | .boneA2 | .boneC2 => .r2
  | .boneB1 => .r1

def GoodBoneClass.sourceShift : GoodBoneClass → Cell
  | .boneA0 | .boneB0 => (0, 0)
  | .boneA2 => (1, 0)
  | .boneB1 => (0, 1)
  | .boneC0 => (1, -2)
  | .boneC2 => (0, -1)

def GoodBoneClass.targetShift : GoodBoneClass → Cell
  | .boneA0 => stepA
  | .boneA2 => (0, -1)
  | .boneB0 => stepC
  | .boneB1 => (-1, 0)
  | .boneC0 => (0, 0)
  | .boneC2 => (2, -2)

def GoodBoneClass.label : GoodBoneClass → MicroLabel
  | .boneA0 | .boneA2 => .two
  | .boneB0 | .boneB1 => .one
  | .boneC0 | .boneC2 => .zero

def GoodBoneClass.step : GoodBoneClass → Cell
  | .boneA0 | .boneC2 => stepA
  | .boneA2 | .boneB1 => stepB
  | .boneB0 | .boneC0 => stepC

def IsPlacementClass {m : ℕ} (placement : LiteralPlacement m)
    (boneClass : GoodBoneClass) : Prop :=
  placement.tile = boneClass.tile ∧
    placementBaseResidue (m + 3) placement.base = boneClass.residue

theorem exists_unique_goodBoneClass {m : ℕ} (placement : LiteralPlacement m)
    (hbone : placement.tile ≠ .stone)
    (htwo : ¬IsThreeOwnerBone placement) :
    ∃! boneClass : GoodBoneClass, IsPlacementClass placement boneClass := by
  rcases htile : placement.tile with _ | _ | _ | _
  · exact (hbone htile).elim
  all_goals
    rcases hrho : placementBaseResidue (m + 3) placement.base with _ | _ | _
  all_goals
    simp [IsThreeOwnerBone, htile, hrho] at htwo
  · refine ⟨.boneA0, ?_, ?_⟩
    · simp [IsPlacementClass, GoodBoneClass.tile, GoodBoneClass.residue,
        htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneA2, ?_, ?_⟩
    · simp [IsPlacementClass, GoodBoneClass.tile, GoodBoneClass.residue,
        htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneB0, ?_, ?_⟩
    · simp [IsPlacementClass, GoodBoneClass.tile, GoodBoneClass.residue,
        htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneB1, ?_, ?_⟩
    · simp [IsPlacementClass, GoodBoneClass.tile, GoodBoneClass.residue,
        htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneC0, ?_, ?_⟩
    · simp [IsPlacementClass, GoodBoneClass.tile, GoodBoneClass.residue,
        htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneC2, ?_, ?_⟩
    · simp [IsPlacementClass, GoodBoneClass.tile, GoodBoneClass.residue,
        htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢

theorem goodBoneClass_step_allowed (boneClass : GoodBoneClass) :
    allowedStep boneClass.label boneClass.step := by
  rcases boneClass <;>
    simp [GoodBoneClass.label, GoodBoneClass.step, allowedStep]

theorem goodBoneClass_target (boneClass : GoodBoneClass) :
    addCell boneClass.sourceShift boneClass.step = boneClass.targetShift := by
  rcases boneClass <;>
    decide

theorem goodBoneClass_profile (boneClass : GoodBoneClass) :
    let source := boneClass.sourceShift
    let target := boneClass.targetShift
    let label := boneClass.label
    (boneOwnerProfile boneClass.tile boneClass.residue).count
        (source, label) = 0 ∧
      (boneOwnerProfile boneClass.tile boneClass.residue).count
        (target, label) = 1 ∧
      (boneOwnerProfile boneClass.tile boneClass.residue).countP
        (fun datum => datum.1 = source) = 2 := by
  rcases boneClass <;> decide

end BenzelProblem6Kernel
