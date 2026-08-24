import BenzelProblem6Kernel.ExposedPlacementEdgeStoneAllSides
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneAAllSides
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneBAllSides
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneCAllSides

/-! # Exact boundary/exposure equivalence for every literal tile side -/

namespace BenzelProblem6Kernel

theorem cellSide_mem_literalPrototypeBoundary_iff
    (tile : ProtoTile) (base cell : Cell) (side : HexSide)
    (hcell : cell ∈
      (protoCells tile).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell side ∈ literalPrototypeBoundary tile base ↔
      neighboringCell cell side ∉
        (protoCells tile).map (translateLocalCell base) := by
  cases tile
  · exact cellSide_mem_stoneBoundary_iff base cell side hcell
  · exact cellSide_mem_boneABoundary_iff base cell side hcell
  · exact cellSide_mem_boneBBoundary_iff base cell side hcell
  · exact cellSide_mem_boneCBoundary_iff base cell side hcell

theorem cellSide_mem_literalPlacementBoundary_iff {m : ℕ}
    (placement : LiteralPlacement m) (cell : Cell) (side : HexSide)
    (hcell : cell ∈ placement.cells) :
    cellBoundaryEdgeAt cell side ∈ literalPlacementBoundary placement ↔
      neighboringCell cell side ∉ placement.cells := by
  exact cellSide_mem_literalPrototypeBoundary_iff
    placement.tile placement.base cell side hcell

end BenzelProblem6Kernel
