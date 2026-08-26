import D4KernelOnly.D4TerminalAccounting

/-! # Every selected-edge endpoint remains on the d=4 terminal contour -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem d4ReversePlacement_mem_reverseTiling {m : ℕ}
    (tiling : D4LiteralTiling m) {placement : LiteralPlacement m}
    (hplacement : placement ∈ d4ShadowPlacementFinset tiling)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges
      (literalPlacementBoundary placement)) :
    edge ∈ reverseLiteralPlacementBoundaryList
      (d4ShadowPlacementFinset tiling).toList := by
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap]
  exact ⟨placement, Finset.mem_toList.mpr hplacement, hedge⟩

theorem d4Edge_mem_complex_of_reversePlacement {m : ℕ}
    (tiling : D4LiteralTiling m) {placement : LiteralPlacement m}
    (hplacement : placement ∈ d4ShadowPlacementFinset tiling)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges
      (literalPlacementBoundary placement)) :
    edge ∈ d4TilingComplexDirectedEdges tiling := by
  rw [d4TilingComplexDirectedEdges, List.mem_append]
  exact Or.inr (d4ReversePlacement_mem_reverseTiling tiling hplacement hedge)

theorem d4SelectedPair_source_mem_terminal {m : ℕ}
    (tiling : D4LiteralTiling m) {selected : LabeledHexEdge}
    (hselected : selected ∈
      (d4ReducedRightmostSkeleton tiling).selectedEdgePairs) :
    selected.source ∈
      edgeSourceFinset (d4ReducedRightmostTerminal tiling).edges := by
  let skeleton := d4ReducedRightmostSkeleton tiling
  obtain ⟨splice, hplacement, hselectedPair,
      selectedCell, hselectedCell, hshared⟩ :=
    skeleton.selectedPair_has_splice hselected
  have haccount := d4Terminal_edgeAccounting_perm tiling
  have hsplit (edge : LabeledHexEdge)
      (hedge : edge ∈ d4TilingComplexDirectedEdges tiling) :
      edge ∈ (d4ReducedRightmostTerminal tiling).edges ∨
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
        d4TilingComplexDirectedEdges tiling :=
      d4Edge_mem_complex_of_reversePlacement tiling
        hplacement halternativePlacement
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
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨alternative, hotherPair, rfl⟩
      have hcellEq : selectedCell = otherCell :=
        side₅_endpoint_owner_unique selectedCell otherCell
          splice.sharedEdge.source hvertexFirst hvertexOther
      have hsharedEq : splice.sharedEdge = otherSplice.sharedEdge := by
        rw [hshared, hotherShared, hcellEq]
      rw [← hsharedEq] at hotherPair
      simp only [selectedEdgePair, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hotherPair
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
        d4TilingComplexDirectedEdges tiling :=
      d4Edge_mem_complex_of_reversePlacement tiling
        hplacement hreverseAlternative
    have halternativeComplex : alternative ∈
        d4TilingComplexDirectedEdges tiling := by
      simpa [reverseLabeledHexEdge_involutive] using
        d4TilingComplexDirectedEdges_reverse_mem tiling hreverseComplex
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
        simp [edgeSourceFinset, selectedEdgePair, reverseLabeledHexEdge]
      have hvertexOther : splice.sharedEdge.target ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt otherCell .side₅)) := by
        rw [← hsource, ← hotherShared]
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨alternative, hotherPair, rfl⟩
      have hcellEq : selectedCell = otherCell :=
        side₅_endpoint_owner_unique selectedCell otherCell
          splice.sharedEdge.target hvertexFirst hvertexOther
      have hsharedEq : splice.sharedEdge = otherSplice.sharedEdge := by
        rw [hshared, hotherShared, hcellEq]
      rw [← hsharedEq] at hotherPair
      simp only [selectedEdgePair, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hotherPair
      rcases hotherPair with heq | heq
      · exact (hneForward heq).elim
      · exact (hneReverse heq).elim

theorem d4Selected_sources_subset_terminal {m : ℕ}
    (tiling : D4LiteralTiling m) :
    edgeSourceFinset
        (d4ReducedRightmostSkeleton tiling).selectedEdgePairs ⊆
      edgeSourceFinset (d4ReducedRightmostTerminal tiling).edges := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  rw [← hsource]
  exact d4SelectedPair_source_mem_terminal tiling hedge

theorem d4Terminal_source_eq_boundaryVertices {m : ℕ}
    (tiling : D4LiteralTiling m) :
    edgeSourceFinset (d4ReducedRightmostTerminal tiling).edges =
      d4TilingBoundaryVertexFinset tiling := by
  apply Finset.Subset.antisymm
  · exact d4Terminal_source_subset_boundaryVertices tiling
  · have hsource := edgeSourceFinset_perm
      (d4Terminal_edgeAccounting_perm tiling)
    rw [d4EdgeSourceFinset_tilingComplex,
      edgeSourceFinset_append] at hsource
    rw [hsource]
    exact Finset.union_subset (Finset.Subset.rfl)
      (d4Selected_sources_subset_terminal tiling)

end FiniteDefects
