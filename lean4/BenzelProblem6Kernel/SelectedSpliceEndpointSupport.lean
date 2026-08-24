import BenzelProblem6Kernel.GeometricSpliceEndpointAlternatives
import BenzelProblem6Kernel.TilingComplexVertexSupport

/-! # Every selected-edge endpoint remains in the terminal contour -/

namespace BenzelProblem6Kernel

theorem side₅_endpoint_owner_unique
    (left right : Cell) (vertex : HexVertex)
    (hleft : vertex ∈ edgeSourceFinset
      (selectedEdgePair (cellBoundaryEdgeAt left .side₅)))
    (hright : vertex ∈ edgeSourceFinset
      (selectedEdgePair (cellBoundaryEdgeAt right .side₅))) :
    left = right := by
  rcases left with ⟨li, lj⟩
  rcases right with ⟨ri, rj⟩
  rcases vertex with ⟨x, y⟩
  simp [edgeSourceFinset, selectedEdgePair,
    reverseLabeledHexEdge, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex,
    hexCellCenter, ShadowStep.neg, shadowA, shadowB, shadowC] at hleft hright
  apply Prod.ext <;> omega

theorem RightmostPeelingSkeleton.selectedPair_has_splice {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements)
    {edge : LabeledHexEdge} (hedge : edge ∈ skeleton.selectedEdgePairs) :
    ∃ (splice : GeometricTileBoundarySplice m),
      splice.placement ∈ placements ∧
      edge ∈ selectedEdgePair splice.sharedEdge ∧
      ∃ cell ∈ splice.placement.cells,
        splice.sharedEdge = cellBoundaryEdgeAt cell .side₅ := by
  induction skeleton with
  | done => simp [RightmostPeelingSkeleton.selectedEdgePairs] at hedge
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      simp only [RightmostPeelingSkeleton.selectedEdgePairs,
        List.mem_append] at hedge
      rcases hedge with hedgeRest | hedgeHere
      · obtain ⟨restSplice, hrestMem, hedgePair,
          cell, hcell, hshared⟩ := ih hedgeRest
        exact ⟨restSplice, Finset.mem_of_mem_erase hrestMem,
          hedgePair, cell, hcell, hshared⟩
      · exact ⟨splice, placement_mem, hedgeHere,
          selectedCell, selectedCell_mem, sharedEdge_exact⟩

theorem GeometricTileBoundarySplice.rotated_mem_tile {m : ℕ}
    (splice : GeometricTileBoundarySplice m)
    {edge : LabeledHexEdge} (hedge : edge ∈ splice.rotatedTileRest) :
    edge ∈ literalPlacementBoundary splice.placement := by
  rw [splice.tile_eq]
  simp only [GeometricTileBoundarySplice.rotatedTileRest,
    List.mem_append] at hedge
  rcases hedge with hsuffix | hprefix
  · exact List.mem_append_right _ (by simp [hsuffix])
  · exact List.mem_append_left _ hprefix

theorem reverseRotated_mem_reversePlacement {m : ℕ}
    (splice : GeometricTileBoundarySplice m)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges splice.rotatedTileRest) :
    edge ∈ reverseReorientedEdges
      (literalPlacementBoundary splice.placement) := by
  apply (mem_reverseReorientedEdges_iff edge _).mpr
  apply splice.rotated_mem_tile
  exact (mem_reverseReorientedEdges_iff edge _).mp hedge

theorem reversePlacement_mem_reverseTiling {m : ℕ}
    (tiling : LiteralTiling m) {placement : LiteralPlacement m}
    (hplacement : placement ∈ tiling.1)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges
      (literalPlacementBoundary placement)) :
    edge ∈ reverseLiteralPlacementBoundaryList tiling.1.toList := by
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap]
  exact ⟨placement, Finset.mem_toList.mpr hplacement, hedge⟩

theorem edge_mem_tilingComplex_of_reversePlacement {m : ℕ}
    (tiling : LiteralTiling m) {placement : LiteralPlacement m}
    (hplacement : placement ∈ tiling.1)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges
      (literalPlacementBoundary placement)) :
    edge ∈ literalTilingComplexDirectedEdges tiling := by
  rw [literalTilingComplexDirectedEdges, List.mem_append]
  exact Or.inr (reversePlacement_mem_reverseTiling tiling hplacement hedge)

theorem selectedPair_source_mem_terminal {m : ℕ}
    (tiling : LiteralTiling m) {selected : LabeledHexEdge}
    (hselected : selected ∈
      (literalTilingRightmostSkeleton tiling).selectedEdgePairs) :
    selected.source ∈
      edgeSourceFinset (literalTilingRightmostTerminal tiling).edges := by
  let skeleton := literalTilingRightmostSkeleton tiling
  obtain ⟨splice, hplacement, hselectedPair,
      selectedCell, hselectedCell, hshared⟩ :=
    skeleton.selectedPair_has_splice hselected
  have hplacementTiling : splice.placement ∈ tiling.1 := hplacement
  have haccount := literalTilingTerminal_edgeAccounting_perm tiling
  have hsplit (edge : LabeledHexEdge)
      (hedge : edge ∈ literalTilingComplexDirectedEdges tiling) :
      edge ∈ (literalTilingRightmostTerminal tiling).edges ∨
        edge ∈ skeleton.selectedEdgePairs := by
    have := haccount.mem_iff.mp hedge
    rwa [List.mem_append] at this
  simp only [selectedEdgePair, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hselectedPair
  rcases hselectedPair with hforward | hreverse
  · subst selected
    obtain ⟨alternative, halternativeRest, hsource,
        hneForward, hneReverse⟩ := splice.exists_source_alternative
    have halternativePlacement : alternative ∈ reverseReorientedEdges
        (literalPlacementBoundary splice.placement) :=
      reverseRotated_mem_reversePlacement splice halternativeRest
    have halternativeComplex : alternative ∈
        literalTilingComplexDirectedEdges tiling :=
      edge_mem_tilingComplex_of_reversePlacement tiling
        hplacementTiling halternativePlacement
    rcases hsplit alternative halternativeComplex with
        hterminal | hselectedAgain
    · simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨alternative, hterminal, hsource⟩
    · obtain ⟨otherSplice, hotherPlacement, hotherPair,
          otherCell, hotherCell, hotherShared⟩ :=
        skeleton.selectedPair_has_splice hselectedAgain
      have hvertexFirst : splice.sharedEdge.source ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt selectedCell .side₅)) := by
        rw [← hshared]
        simp [edgeSourceFinset, selectedEdgePair]
      have hvertexOther : splice.sharedEdge.source ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt otherCell .side₅)) := by
        rw [← hsource, ← hotherShared]
        simp only [edgeSourceFinset, List.mem_toFinset,
          List.mem_map]
        exact ⟨alternative, hotherPair, rfl⟩
      have hcellEq : selectedCell = otherCell :=
        side₅_endpoint_owner_unique selectedCell otherCell
          splice.sharedEdge.source hvertexFirst hvertexOther
      have hsharedEq : splice.sharedEdge = otherSplice.sharedEdge := by
        rw [hshared, hotherShared, hcellEq]
      rw [← hsharedEq] at hotherPair
      simp only [selectedEdgePair, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hotherPair
      rcases hotherPair with heq | heq
      · exact (hneForward heq).elim
      · exact (hneReverse heq).elim
  · subst selected
    obtain ⟨alternative, halternativeRest, hsource,
        hneForward, hneReverse⟩ := splice.exists_target_alternative
    have hreverseAlternative : reverseLabeledHexEdge alternative ∈
        reverseReorientedEdges
          (literalPlacementBoundary splice.placement) := by
      apply (mem_reverseReorientedEdges_iff _ _).mpr
      simpa [reverseLabeledHexEdge_involutive] using
        splice.rotated_mem_tile halternativeRest
    have hreverseComplex : reverseLabeledHexEdge alternative ∈
        literalTilingComplexDirectedEdges tiling :=
      edge_mem_tilingComplex_of_reversePlacement tiling
        hplacementTiling hreverseAlternative
    have halternativeComplex : alternative ∈
        literalTilingComplexDirectedEdges tiling := by
      simpa [reverseLabeledHexEdge_involutive] using
        literalTilingComplexDirectedEdges_reverse_mem tiling hreverseComplex
    rcases hsplit alternative halternativeComplex with
        hterminal | hselectedAgain
    · simp only [reverseLabeledHexEdge, edgeSourceFinset,
        List.mem_toFinset, List.mem_map]
      exact ⟨alternative, hterminal, hsource⟩
    · obtain ⟨otherSplice, hotherPlacement, hotherPair,
          otherCell, hotherCell, hotherShared⟩ :=
        skeleton.selectedPair_has_splice hselectedAgain
      have hvertexFirst : splice.sharedEdge.target ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt selectedCell .side₅)) := by
        rw [← hshared]
        simp [edgeSourceFinset, selectedEdgePair,
          reverseLabeledHexEdge]
      have hvertexOther : splice.sharedEdge.target ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt otherCell .side₅)) := by
        rw [← hsource, ← hotherShared]
        simp only [edgeSourceFinset, List.mem_toFinset,
          List.mem_map]
        exact ⟨alternative, hotherPair, rfl⟩
      have hcellEq : selectedCell = otherCell :=
        side₅_endpoint_owner_unique selectedCell otherCell
          splice.sharedEdge.target hvertexFirst hvertexOther
      have hsharedEq : splice.sharedEdge = otherSplice.sharedEdge := by
        rw [hshared, hotherShared, hcellEq]
      rw [← hsharedEq] at hotherPair
      simp only [selectedEdgePair, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hotherPair
      rcases hotherPair with heq | heq
      · exact (hneForward heq).elim
      · exact (hneReverse heq).elim

theorem selected_sources_subset_terminal {m : ℕ}
    (tiling : LiteralTiling m) :
    edgeSourceFinset
        (literalTilingRightmostSkeleton tiling).selectedEdgePairs ⊆
      edgeSourceFinset (literalTilingRightmostTerminal tiling).edges := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset,
    List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  rw [← hsource]
  exact selectedPair_source_mem_terminal tiling hedge

theorem terminal_source_eq_boundaryVertices {m : ℕ}
    (tiling : LiteralTiling m) :
    edgeSourceFinset (literalTilingRightmostTerminal tiling).edges =
      tilingBoundaryVertexFinset tiling := by
  apply Finset.Subset.antisymm
  · exact terminal_source_subset_boundaryVertices tiling
  · have hsource := edgeSourceFinset_perm
      (literalTilingTerminal_edgeAccounting_perm tiling)
    rw [edgeSourceFinset_tilingComplex,
      edgeSourceFinset_append] at hsource
    rw [hsource]
    exact Finset.union_subset (Finset.Subset.rfl)
      (selected_sources_subset_terminal tiling)

end BenzelProblem6Kernel
