import BenzelProblem6Kernel.TilingComplexEdgePairs

/-! # A literal tile boundary never contains both orientations of one edge -/

namespace BenzelProblem6Kernel

theorem literalPlacementBoundary_reverse_not_mem {m : ℕ}
    (placement : LiteralPlacement m) {edge : LabeledHexEdge}
    (hedge : edge ∈ literalPlacementBoundary placement) :
    reverseLabeledHexEdge edge ∉ literalPlacementBoundary placement := by
  obtain ⟨cell, hcell, hedgeCell⟩ :=
    literalPlacementBoundary_edge_has_cell placement hedge
  obtain ⟨side, hside⟩ := labeledCellBoundary_edge_has_side hedgeCell
  have hsideBoundary : cellBoundaryEdgeAt cell side ∈
      literalPlacementBoundary placement := by
    rwa [hside]
  have hneighborNot : neighboringCell cell side ∉ placement.cells :=
    (cellSide_mem_literalPlacementBoundary_iff
      placement cell side hcell).mp hsideBoundary
  intro hreverse
  obtain ⟨other, hother, hotherEdge⟩ :=
    literalPlacementBoundary_edge_has_cell placement hreverse
  have hreverseSide : reverseLabeledHexEdge
      (cellBoundaryEdgeAt cell side) ∈ labeledCellBoundary other := by
    rwa [hside]
  have hotherEq : other = neighboringCell cell side :=
    (reverse_edge_mem_labeledCellBoundary_iff
      cell other side).mp hreverseSide
  exact hneighborNot (by rwa [← hotherEq])

end BenzelProblem6Kernel
