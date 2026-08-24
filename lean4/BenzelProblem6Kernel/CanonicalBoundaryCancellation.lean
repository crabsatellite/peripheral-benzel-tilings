import BenzelProblem6Kernel.BoundaryTranslation

/-!
# Canonical finite boundary-cancellation certificates
-/

namespace BenzelProblem6Kernel

theorem canonical_stone_boundary_cancel :
    prototypeCellBoundaryXor .stone (0, 0) =
      prototypeOuterBoundaryKeys .stone (0, 0) := by
  decide

theorem canonical_boneA_boundary_cancel :
    prototypeCellBoundaryXor .boneA (0, 0) =
      prototypeOuterBoundaryKeys .boneA (0, 0) := by
  decide

theorem canonical_boneB_boundary_cancel :
    prototypeCellBoundaryXor .boneB (0, 0) =
      prototypeOuterBoundaryKeys .boneB (0, 0) := by
  decide

theorem canonical_boneC_boundary_cancel :
    prototypeCellBoundaryXor .boneC (0, 0) =
      prototypeOuterBoundaryKeys .boneC (0, 0) := by
  decide

theorem canonical_prototype_boundary_cancel (tile : ProtoTile) :
    prototypeCellBoundaryXor tile (0, 0) =
      prototypeOuterBoundaryKeys tile (0, 0) := by
  cases tile
  · exact canonical_stone_boundary_cancel
  · exact canonical_boneA_boundary_cancel
  · exact canonical_boneB_boundary_cancel
  · exact canonical_boneC_boundary_cancel

theorem prototype_boundary_internal_edges_cancel
    (tile : ProtoTile) (base : Cell) :
    prototypeCellBoundaryXor tile base =
      prototypeOuterBoundaryKeys tile base := by
  rw [prototypeCellBoundaryXor_translate,
    prototypeOuterBoundaryKeys_translate,
    canonical_prototype_boundary_cancel]

theorem literalPlacementBoundaryKeys_eq_cells {m : ℕ}
    (placement : LiteralPlacement m) :
    xorCellBoundaryList placement.cells =
      literalPlacementBoundaryKeys placement := by
  exact prototype_boundary_internal_edges_cancel placement.tile placement.base

end BenzelProblem6Kernel
