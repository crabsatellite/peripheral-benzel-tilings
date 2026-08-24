import BenzelProblem6Kernel.TilingComplexEdgeNodup

/-! # Reverse-pair closure of the complete tiling-complex edge list -/

namespace BenzelProblem6Kernel

theorem labeledCellBoundary_edge_has_side
    {cell : Cell} {edge : LabeledHexEdge}
    (hedge : edge ∈ labeledCellBoundary cell) :
    ∃ side : HexSide, cellBoundaryEdgeAt cell side = edge := by
  rw [labeledCellBoundary_eq_allEdges] at hedge
  simp only [allCellBoundaryEdges, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hedge
  rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.side₀, rfl⟩
  · exact ⟨.side₁, rfl⟩
  · exact ⟨.side₂, rfl⟩
  · exact ⟨.side₃, rfl⟩
  · exact ⟨.side₄, rfl⟩
  · exact ⟨.side₅, rfl⟩

theorem reverse_mem_reverseTiling_of_outer_mem {m : ℕ}
    (tiling : LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ literalReducedPeripheralBoundary m) :
    reverseLabeledHexEdge edge ∈
      reverseLiteralPlacementBoundaryList tiling.1.toList := by
  obtain ⟨datum, hdatum, hedgeDatum⟩ :=
    mem_literalReducedPeripheralBoundary_exists_datum hedge
  have hinside := (isInsidePeripheralEdge_iff_mem
    m datum.1 datum.2).mpr hdatum
  let regionCell : BenzelCell (m + 5) := ⟨datum.1, hinside.1⟩
  obtain ⟨placement, hplacement, hunique⟩ := tiling.2 regionCell
  have hneighborPlacement : neighboringCell datum.1 datum.2 ∉
      placement.cells := by
    intro hneighbor
    exact hinside.2 (placement.2 _ hneighbor)
  have hplacementEdge : cellBoundaryEdgeAt datum.1 datum.2 ∈
      literalPlacementBoundary placement :=
    (cellSide_mem_literalPlacementBoundary_iff
      placement datum.1 datum.2 hplacement.2).mpr hneighborPlacement
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap]
  refine ⟨placement, Finset.mem_toList.mpr hplacement.1, ?_⟩
  apply (mem_reverseReorientedEdges_iff
    (reverseLabeledHexEdge edge) _).mpr
  rw [reverseLabeledHexEdge_involutive, ← hedgeDatum]
  exact hplacementEdge

theorem reverse_mem_complex_of_reverseTiling_mem {m : ℕ}
    (tiling : LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈
      reverseLiteralPlacementBoundaryList tiling.1.toList) :
    reverseLabeledHexEdge edge ∈
      literalTilingComplexDirectedEdges tiling := by
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap] at hedge
  obtain ⟨placement, hplacementList, hedgePlacement⟩ := hedge
  have hplacementMem : placement ∈ tiling.1 :=
    Finset.mem_toList.mp hplacementList
  have hboundary : reverseLabeledHexEdge edge ∈
      literalPlacementBoundary placement :=
    (mem_reverseReorientedEdges_iff edge _).mp hedgePlacement
  obtain ⟨cell, hcell, hcellEdge⟩ :=
    literalPlacementBoundary_edge_has_cell placement hboundary
  obtain ⟨side, hside⟩ :=
    labeledCellBoundary_edge_has_side hcellEdge
  have hsideBoundary : cellBoundaryEdgeAt cell side ∈
      literalPlacementBoundary placement := by
    rw [hside]
    exact hboundary
  have hneighborNot : neighboringCell cell side ∉ placement.cells :=
    (cellSide_mem_literalPlacementBoundary_iff
      placement cell side hcell).mp hsideBoundary
  by_cases hneighborRegion : inPeripheralBenzel (m + 5)
      (neighboringCell cell side)
  · let neighborRegionCell : BenzelCell (m + 5) :=
      ⟨neighboringCell cell side, hneighborRegion⟩
    obtain ⟨other, hother, hotherUnique⟩ :=
      tiling.2 neighborRegionCell
    have hcellNotOther : cell ∉ other.cells := by
      intro hcellOther
      let cellRegion : BenzelCell (m + 5) :=
        ⟨cell, placement.2 cell hcell⟩
      obtain ⟨covering, hcovering, hunique⟩ := tiling.2 cellRegion
      have hplacementEq : placement = covering :=
        hunique placement ⟨hplacementMem, hcell⟩
      have hotherEq : other = covering :=
        hunique other ⟨hother.1, hcellOther⟩
      have hsame : other = placement :=
        hotherEq.trans hplacementEq.symm
      exact hneighborNot (by
        rw [← hsame]
        exact hother.2)
    have hotherExposed : neighboringCell
        (neighboringCell cell side) (oppositeHexSide side) ∉
          other.cells := by
      simpa [neighboringCell_opposite] using hcellNotOther
    have hotherBoundary : cellBoundaryEdgeAt
        (neighboringCell cell side) (oppositeHexSide side) ∈
          literalPlacementBoundary other :=
      (cellSide_mem_literalPlacementBoundary_iff other
        (neighboringCell cell side) (oppositeHexSide side)
        hother.2).mpr hotherExposed
    have hedgeOther : edge ∈ literalPlacementBoundary other := by
      rw [cellBoundaryEdgeAt_neighbor_exact, hside,
        reverseLabeledHexEdge_involutive] at hotherBoundary
      exact hotherBoundary
    rw [literalTilingComplexDirectedEdges, List.mem_append]
    right
    rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap]
    refine ⟨other, Finset.mem_toList.mpr hother.1, ?_⟩
    apply (mem_reverseReorientedEdges_iff
      (reverseLabeledHexEdge edge) _).mpr
    rwa [reverseLabeledHexEdge_involutive]
  · have hinsideEdge : IsInsidePeripheralEdge m cell side :=
      ⟨placement.2 cell hcell, hneighborRegion⟩
    have hdatum : (cell, side) ∈ literalPeripheralIncidences m :=
      (isInsidePeripheralEdge_iff_mem m cell side).mp hinsideEdge
    rw [literalTilingComplexDirectedEdges, List.mem_append]
    left
    simp only [literalReducedPeripheralBoundary, List.mem_map,
      List.mem_reverse]
    exact ⟨(cell, side), hdatum, hside⟩

theorem literalTilingComplexDirectedEdges_reverse_mem {m : ℕ}
    (tiling : LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ literalTilingComplexDirectedEdges tiling) :
    reverseLabeledHexEdge edge ∈
      literalTilingComplexDirectedEdges tiling := by
  rw [literalTilingComplexDirectedEdges, List.mem_append] at hedge ⊢
  rcases hedge with hedgeOuter | hedgeTiles
  · exact Or.inr (reverse_mem_reverseTiling_of_outer_mem tiling hedgeOuter)
  · simpa [literalTilingComplexDirectedEdges] using
      reverse_mem_complex_of_reverseTiling_mem tiling hedgeTiles

theorem literalTilingComplexDirectedEdges_reverse_iff {m : ℕ}
    (tiling : LiteralTiling m) (edge : LabeledHexEdge) :
    reverseLabeledHexEdge edge ∈ literalTilingComplexDirectedEdges tiling ↔
      edge ∈ literalTilingComplexDirectedEdges tiling := by
  constructor
  · intro hedge
    simpa [reverseLabeledHexEdge_involutive] using
      literalTilingComplexDirectedEdges_reverse_mem tiling hedge
  · exact literalTilingComplexDirectedEdges_reverse_mem tiling

end BenzelProblem6Kernel
