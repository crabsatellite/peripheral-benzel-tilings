import D4KernelOnly.GeneralClassZeroTerminalAccounting

/-! # Selected-edge endpoints remain on the class-zero terminal contour -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czReversePlacement_mem_reverseTiling
    {s r : ℕ} (tiling : CZLiteralTiling s r)
    {placement : LiteralPlacement (2 * s + r - 2)}
    (hplacement : placement ∈ offsetShadowPlacementFinset tiling)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges (literalPlacementBoundary placement)) :
    edge ∈ reverseLiteralPlacementBoundaryList
      (offsetShadowPlacementFinset tiling).toList := by
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap]
  exact ⟨placement, Finset.mem_toList.mpr hplacement, hedge⟩

theorem czEdge_mem_complex_of_reversePlacement
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r)
    {placement : LiteralPlacement (2 * s + r - 2)}
    (hplacement : placement ∈ offsetShadowPlacementFinset tiling)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges (literalPlacementBoundary placement)) :
    edge ∈ czTilingComplexDirectedEdges hs hr tiling := by
  rw [czTilingComplexDirectedEdges, List.mem_append]
  exact Or.inr (czReversePlacement_mem_reverseTiling tiling hplacement hedge)

theorem czSelectedPair_source_mem_terminal
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) {selected : LabeledHexEdge}
    (hselected : selected ∈
      (czReducedRightmostSkeleton hs hr tiling).selectedEdgePairs) :
    selected.source ∈
      edgeSourceFinset (czReducedRightmostTerminal hs hr tiling).edges := by
  let skeleton := czReducedRightmostSkeleton hs hr tiling
  obtain ⟨splice, hplacement, hselectedPair,
      selectedCell, hselectedCell, hshared⟩ :=
    skeleton.selectedPair_has_splice hselected
  have haccount := czTerminal_edgeAccounting_perm hs hr tiling
  have hsplit (edge : LabeledHexEdge)
      (hedge : edge ∈ czTilingComplexDirectedEdges hs hr tiling) :
      edge ∈ (czReducedRightmostTerminal hs hr tiling).edges ∨
        edge ∈ skeleton.selectedEdgePairs := by
    have := haccount.mem_iff.mp hedge
    rwa [List.mem_append] at this
  simp only [selectedEdgePair, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hselectedPair
  rcases hselectedPair with hforward | hreverse
  · subst selected
    obtain ⟨alternative, halternativeRest, hsource,
        hneForward, hneReverse⟩ := splice.exists_source_alternative
    have hp : alternative ∈ reverseReorientedEdges
        (literalPlacementBoundary splice.placement) :=
      reverseRotated_mem_reversePlacement splice halternativeRest
    have hc : alternative ∈ czTilingComplexDirectedEdges hs hr tiling :=
      czEdge_mem_complex_of_reversePlacement hs hr tiling hplacement hp
    rcases hsplit alternative hc with ht | hselectedAgain
    · simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨alternative, ht, hsource⟩
    · obtain ⟨otherSplice, hotherPlacement, hotherPair,
          otherCell, hotherCell, hotherShared⟩ :=
        skeleton.selectedPair_has_splice hselectedAgain
      have hv1 : splice.sharedEdge.source ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt selectedCell .side₅)) := by
        rw [← hshared]
        simp [edgeSourceFinset, selectedEdgePair]
      have hv2 : splice.sharedEdge.source ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt otherCell .side₅)) := by
        rw [← hsource, ← hotherShared]
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨alternative, hotherPair, rfl⟩
      have hcellEq := side₅_endpoint_owner_unique selectedCell otherCell
        splice.sharedEdge.source hv1 hv2
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
    have hp : reverseLabeledHexEdge alternative ∈ reverseReorientedEdges
        (literalPlacementBoundary splice.placement) := by
      apply (mem_reverseReorientedEdges_iff _ _).mpr
      simpa [reverseLabeledHexEdge_involutive] using
        splice.rotated_mem_tile halternativeRest
    have hrc : reverseLabeledHexEdge alternative ∈
        czTilingComplexDirectedEdges hs hr tiling :=
      czEdge_mem_complex_of_reversePlacement hs hr tiling hplacement hp
    have hc : alternative ∈ czTilingComplexDirectedEdges hs hr tiling := by
      simpa [reverseLabeledHexEdge_involutive] using
        czTilingComplexDirectedEdges_reverse_mem hs hr tiling hrc
    rcases hsplit alternative hc with ht | hselectedAgain
    · simp only [reverseLabeledHexEdge, edgeSourceFinset,
        List.mem_toFinset, List.mem_map]
      exact ⟨alternative, ht, hsource⟩
    · obtain ⟨otherSplice, hotherPlacement, hotherPair,
          otherCell, hotherCell, hotherShared⟩ :=
        skeleton.selectedPair_has_splice hselectedAgain
      have hv1 : splice.sharedEdge.target ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt selectedCell .side₅)) := by
        rw [← hshared]
        simp [edgeSourceFinset, selectedEdgePair, reverseLabeledHexEdge]
      have hv2 : splice.sharedEdge.target ∈ edgeSourceFinset
          (selectedEdgePair (cellBoundaryEdgeAt otherCell .side₅)) := by
        rw [← hsource, ← hotherShared]
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨alternative, hotherPair, rfl⟩
      have hcellEq := side₅_endpoint_owner_unique selectedCell otherCell
        splice.sharedEdge.target hv1 hv2
      have hsharedEq : splice.sharedEdge = otherSplice.sharedEdge := by
        rw [hshared, hotherShared, hcellEq]
      rw [← hsharedEq] at hotherPair
      simp only [selectedEdgePair, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hotherPair
      rcases hotherPair with heq | heq
      · exact (hneForward heq).elim
      · exact (hneReverse heq).elim

theorem czSelected_sources_subset_terminal
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    edgeSourceFinset
        (czReducedRightmostSkeleton hs hr tiling).selectedEdgePairs ⊆
      edgeSourceFinset (czReducedRightmostTerminal hs hr tiling).edges := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  rw [← hsource]
  exact czSelectedPair_source_mem_terminal hs hr tiling hedge

theorem czTerminal_source_eq_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    edgeSourceFinset (czReducedRightmostTerminal hs hr tiling).edges =
      offsetTilingBoundaryVertexFinset tiling := by
  apply Finset.Subset.antisymm
  · exact czTerminal_source_subset_boundaryVertices hs hr tiling
  · have hsource := edgeSourceFinset_perm (czTerminal_edgeAccounting_perm hs hr tiling)
    rw [czEdgeSourceFinset_tilingComplex hs hr tiling,
      edgeSourceFinset_append] at hsource
    rw [hsource]
    exact Finset.union_subset Finset.Subset.rfl
      (czSelected_sources_subset_terminal hs hr tiling)

end FiniteDefects
