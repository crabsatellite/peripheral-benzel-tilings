import BenzelProblem6Kernel.ComponentEnergy
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Zero-corner incidence components contain only in-phase stones
-/

namespace BenzelProblem6Kernel

def IsInPhaseStone {m : ℕ} (placement : LiteralPlacement m) : Prop :=
  placement.tile = .stone ∧
    placementBaseResidue (m + 3) placement.base = .r0

theorem literalPlacementEnergy_nonnegative {m : ℕ}
    (placement : LiteralPlacement m) : 0 ≤ literalPlacementEnergy placement := by
  rw [literal_placement_energy_classification]
  split_ifs <;> norm_num

theorem literalPlacementEnergy_eq_zero_iff {m : ℕ}
    (placement : LiteralPlacement m) :
    literalPlacementEnergy placement = 0 ↔ IsInPhaseStone placement := by
  rw [literal_placement_energy_classification]
  rcases htile : placement.tile with _ | _ | _ | _ <;>
    rcases hrho : placementBaseResidue (m + 3) placement.base with _ | _ | _ <;>
    simp [IsInPhaseStone, IsWrongPhaseStone, IsThreeOwnerBone,
      htile, hrho]

theorem component_placements_inPhase_of_noCorners {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent)
    (hcorners : (componentCornerOwners tiling component).card = 0)
    (placement : TilingPlacementNode tiling)
    (hplacement : placement ∈ componentPlacements tiling component) :
    IsInPhaseStone placement.1 := by
  have hsum := component_tile_energy_eq_corners tiling component
  rw [hcorners] at hsum
  simp only [Nat.cast_zero, mul_zero] at hsum
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun item _ => literalPlacementEnergy_nonnegative item.1)).1 hsum
    placement hplacement
  exact (literalPlacementEnergy_eq_zero_iff placement.1).1 hzero

end BenzelProblem6Kernel
