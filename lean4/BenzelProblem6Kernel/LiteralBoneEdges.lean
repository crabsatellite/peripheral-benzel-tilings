import BenzelProblem6Kernel.LiteralTileEnergy
import BenzelProblem6Kernel.NoCycles

/-!
# Literal two-owner bone edge certificates

Each profile records `(owner shift, micro-label)` for the three cells of the
translated prototile. The six energy-one phases are then identified with the
paper's label-preserving directed edges.
-/

namespace BenzelProblem6Kernel

def localOwnerDatum (baseResidue : Res3) (cell : LocalCell) :
    Cell × MicroLabel :=
  (ownerShift baseResidue cell, localLabel baseResidue cell)

def boneOwnerProfile (tile : ProtoTile) (baseResidue : Res3) :
    List (Cell × MicroLabel) :=
  (protoCells tile).map (localOwnerDatum baseResidue)

theorem boneA_r0_profile :
    boneOwnerProfile .boneA .r0 =
      [((0, 0), .zero), ((0, 0), .one), (stepA, .two)] := by
  decide

theorem boneA_r2_profile :
    boneOwnerProfile .boneA .r2 =
      [((0, -1), .two), ((1, 0), .zero), ((1, 0), .one)] := by
  decide

theorem boneB_r0_profile :
    boneOwnerProfile .boneB .r0 =
      [((0, 0), .zero), ((0, 0), .two), (stepC, .one)] := by
  decide

theorem boneB_r1_profile :
    boneOwnerProfile .boneB .r1 =
      [((-1, 0), .one), ((0, 1), .zero), ((0, 1), .two)] := by
  decide

theorem boneC_r0_profile :
    boneOwnerProfile .boneC .r0 =
      [((0, 0), .zero), ((1, -2), .two), ((1, -2), .one)] := by
  decide

theorem boneC_r2_profile :
    boneOwnerProfile .boneC .r2 =
      [((0, -1), .two), ((0, -1), .one), ((2, -2), .zero)] := by
  decide

theorem boneA_r0_allowed : allowedStep .two stepA := by
  simp [allowedStep]

theorem boneA_r2_allowed :
    allowedStep .two stepB := by
  simp [allowedStep]

theorem boneB_r0_allowed : allowedStep .one stepC := by
  simp [allowedStep]

theorem boneB_r1_allowed :
    allowedStep .one stepB := by
  simp [allowedStep]

theorem boneC_r0_allowed :
    allowedStep .zero stepC := by
  simp [allowedStep]

theorem boneC_r2_allowed : allowedStep .zero stepA := by
  simp [allowedStep]

theorem boneA_r0_target_eq : addCell (0, 0) stepA = stepA := by decide
theorem boneA_r2_target_eq : addCell (1, 0) stepB = (0, -1) := by decide
theorem boneB_r0_target_eq : addCell (0, 0) stepC = stepC := by decide
theorem boneB_r1_target_eq : addCell (0, 1) stepB = (-1, 0) := by decide
theorem boneC_r0_target_eq : addCell (1, -2) stepC = (0, 0) := by decide
theorem boneC_r2_target_eq : addCell (0, -1) stepA = (2, -2) := by decide

theorem boneA_three_owner_profile :
    boneOwnerProfile .boneA .r1 =
      [((-1, 0), .one), ((1, -1), .two), ((2, 0), .zero)] := by
  decide

theorem boneB_three_owner_profile :
    boneOwnerProfile .boneB .r2 =
      [((0, -1), .two), ((-1, 1), .one), ((0, 2), .zero)] := by
  decide

theorem boneC_three_owner_profile :
    boneOwnerProfile .boneC .r1 =
      [((-1, 0), .one), ((1, -1), .zero), ((2, -3), .two)] := by
  decide

theorem all_two_owner_bone_profiles :
    boneOwnerProfile .boneA .r0 =
        [((0, 0), .zero), ((0, 0), .one), (stepA, .two)] ∧
    boneOwnerProfile .boneA .r2 =
        [((0, -1), .two), ((1, 0), .zero), ((1, 0), .one)] ∧
    boneOwnerProfile .boneB .r0 =
        [((0, 0), .zero), ((0, 0), .two), (stepC, .one)] ∧
    boneOwnerProfile .boneB .r1 =
        [((-1, 0), .one), ((0, 1), .zero), ((0, 1), .two)] ∧
    boneOwnerProfile .boneC .r0 =
        [((0, 0), .zero), ((1, -2), .two), ((1, -2), .one)] ∧
    boneOwnerProfile .boneC .r2 =
        [((0, -1), .two), ((0, -1), .one), ((2, -2), .zero)] := by
  exact ⟨boneA_r0_profile, boneA_r2_profile, boneB_r0_profile,
    boneB_r1_profile, boneC_r0_profile, boneC_r2_profile⟩

theorem all_two_owner_bone_directions_allowed :
    allowedStep .two stepA ∧ allowedStep .two stepB ∧
    allowedStep .one stepC ∧ allowedStep .one stepB ∧
    allowedStep .zero stepC ∧ allowedStep .zero stepA := by
  exact ⟨boneA_r0_allowed, boneA_r2_allowed, boneB_r0_allowed,
    boneB_r1_allowed, boneC_r0_allowed, boneC_r2_allowed⟩

end BenzelProblem6Kernel
