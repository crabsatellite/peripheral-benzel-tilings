import BenzelProblem6Kernel.ExposedPlacementEdgeStone
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneA
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneB
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneC

namespace BenzelProblem6Kernel

theorem exposed_side₅_mem_literalPrototypeBoundary
    (tile : ProtoTile) (base cell : Cell)
    (hcell : cell ∈
      (protoCells tile).map (translateLocalCell base))
    (hexposed : neighboringCell cell .side₅ ∉
      (protoCells tile).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₅ ∈
      literalPrototypeBoundary tile base := by
  cases tile
  · exact exposed_side₅_mem_stoneBoundary base cell hcell hexposed
  · exact exposed_side₅_mem_boneABoundary base cell hcell hexposed
  · exact exposed_side₅_mem_boneBBoundary base cell hcell hexposed
  · exact exposed_side₅_mem_boneCBoundary base cell hcell hexposed

theorem exposed_side₅_mem_literalPlacementBoundary
    {m : ℕ} (placement : LiteralPlacement m) (cell : Cell)
    (hcell : cell ∈ placement.cells)
    (hexposed : neighboringCell cell .side₅ ∉ placement.cells) :
    cellBoundaryEdgeAt cell .side₅ ∈
      literalPlacementBoundary placement := by
  exact exposed_side₅_mem_literalPrototypeBoundary
    placement.tile placement.base cell hcell hexposed

end BenzelProblem6Kernel
