import BenzelProblem6Kernel.ContinuousBoundaryVertexFinset

/-! # Vertex support of the tiling complex and terminal contour -/

namespace BenzelProblem6Kernel

theorem edgeSourceFinset_append (left right : List LabeledHexEdge) :
    edgeSourceFinset (left ++ right) =
      edgeSourceFinset left ∪ edgeSourceFinset right := by
  ext vertex
  simp [edgeSourceFinset]

theorem edgeSourceFinset_reversePlacementList {m : ℕ}
    (placements : List (LiteralPlacement m)) :
    edgeSourceFinset (reverseLiteralPlacementBoundaryList placements) =
      placements.toFinset.biUnion placementBoundaryVertexFinset := by
  induction placements with
  | nil => simp [reverseLiteralPlacementBoundaryList, edgeSourceFinset]
  | cons placement rest ih =>
      change edgeSourceFinset
        (reverseReorientedEdges (literalPlacementBoundary placement) ++
          reverseLiteralPlacementBoundaryList rest) = _
      rw [edgeSourceFinset_append,
        placement_reverse_source_eq_source, ih]
      ext vertex
      simp

theorem edgeSourceFinset_reverseTilingList {m : ℕ}
    (tiling : LiteralTiling m) :
    edgeSourceFinset
        (reverseLiteralPlacementBoundaryList tiling.1.toList) =
      tilingBoundaryVertexFinset tiling := by
  rw [edgeSourceFinset_reversePlacementList,
    tilingBoundaryVertexFinset]
  congr 1
  ext placement
  simp

theorem outer_edge_mem_some_placement {m : ℕ}
    (tiling : LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ literalReducedPeripheralBoundary m) :
    ∃ placement ∈ tiling.1,
      edge ∈ literalPlacementBoundary placement := by
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
  refine ⟨placement, hplacement.1, ?_⟩
  rw [← hedgeDatum]
  exact hplacementEdge

theorem outer_source_subset_tilingBoundary {m : ℕ}
    (tiling : LiteralTiling m) :
    edgeSourceFinset (literalReducedPeripheralBoundary m) ⊆
      tilingBoundaryVertexFinset tiling := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset,
    List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  obtain ⟨placement, hplacement, hedgePlacement⟩ :=
    outer_edge_mem_some_placement tiling hedge
  rw [tilingBoundaryVertexFinset, Finset.mem_biUnion]
  refine ⟨placement, hplacement, ?_⟩
  simp only [placementBoundaryVertexFinset,
    prototypeBoundaryVertexFinset, edgeSourceFinset,
    List.mem_toFinset, List.mem_map]
  exact ⟨edge, hedgePlacement, hsource⟩

theorem edgeSourceFinset_tilingComplex {m : ℕ}
    (tiling : LiteralTiling m) :
    edgeSourceFinset (literalTilingComplexDirectedEdges tiling) =
      tilingBoundaryVertexFinset tiling := by
  rw [literalTilingComplexDirectedEdges, edgeSourceFinset_append,
    edgeSourceFinset_reverseTilingList]
  exact Finset.union_eq_right.mpr (outer_source_subset_tilingBoundary tiling)

theorem edgeSourceFinset_perm {left right : List LabeledHexEdge}
    (hperm : List.Perm left right) :
    edgeSourceFinset left = edgeSourceFinset right := by
  ext vertex
  change vertex ∈ (left.map LabeledHexEdge.source).toFinset ↔
    vertex ∈ (right.map LabeledHexEdge.source).toFinset
  simp only [List.mem_toFinset]
  exact (hperm.map LabeledHexEdge.source).mem_iff

theorem terminal_source_subset_boundaryVertices {m : ℕ}
    (tiling : LiteralTiling m) :
    edgeSourceFinset (literalTilingRightmostTerminal tiling).edges ⊆
      tilingBoundaryVertexFinset tiling := by
  have hsource := edgeSourceFinset_perm
    (literalTilingTerminal_edgeAccounting_perm tiling)
  rw [edgeSourceFinset_tilingComplex,
    edgeSourceFinset_append] at hsource
  rw [hsource]
  exact Finset.subset_union_left

end BenzelProblem6Kernel
