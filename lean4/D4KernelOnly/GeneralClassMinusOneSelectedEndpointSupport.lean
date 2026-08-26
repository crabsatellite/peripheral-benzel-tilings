import D4KernelOnly.GeneralClassMinusOneTerminalSources

/-! # Selected-edge endpoints remain on the class-minus-one terminal contour -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem cmoReversePlacement_mem_reverseTiling
    {s r : ℕ} (tiling : CMOLiteralTiling s r)
    {placement : LiteralPlacement (2 * s + r - 1)}
    (hplacement : placement ∈ offsetShadowPlacementFinset tiling)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges
      (literalPlacementBoundary placement)) :
    edge ∈ reverseLiteralPlacementBoundaryList
      (offsetShadowPlacementFinset tiling).toList := by
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap]
  exact ⟨placement, Finset.mem_toList.mpr hplacement, hedge⟩

theorem cmoEdge_mem_complex_of_reversePlacement
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {placement : LiteralPlacement (2 * s + r - 1)}
    (hplacement : placement ∈ offsetShadowPlacementFinset tiling)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ reverseReorientedEdges
      (literalPlacementBoundary placement)) :
    edge ∈ cmoTilingComplexDirectedEdges hs tiling := by
  rw [cmoTilingComplexDirectedEdges, List.mem_append]
  exact Or.inr (cmoReversePlacement_mem_reverseTiling tiling hplacement hedge)

theorem cmoSelectedPair_source_mem_terminal
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {selected : LabeledHexEdge}
    (hselected : selected ∈
      (cmoReducedRightmostSkeleton hs tiling).selectedEdgePairs) :
    selected.source ∈
      edgeSourceFinset (cmoReducedRightmostTerminal hs tiling).edges := by
  let skeleton := cmoReducedRightmostSkeleton hs tiling
  obtain ⟨splice, hplacement, hselectedPair,
      selectedCell, hselectedCell, hshared⟩ :=
    skeleton.selectedPair_has_splice hselected
  have haccount := cmoTerminal_edgeAccounting_perm hs tiling
  have hsplit (edge : LabeledHexEdge)
      (hedge : edge ∈ cmoTilingComplexDirectedEdges hs tiling) :
      edge ∈ (cmoReducedRightmostTerminal hs tiling).edges ∨
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
        cmoTilingComplexDirectedEdges hs tiling :=
      cmoEdge_mem_complex_of_reversePlacement hs tiling
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
        cmoTilingComplexDirectedEdges hs tiling :=
      cmoEdge_mem_complex_of_reversePlacement hs tiling
        hplacement hreverseAlternative
    have halternativeComplex : alternative ∈
        cmoTilingComplexDirectedEdges hs tiling := by
      simpa [reverseLabeledHexEdge_involutive] using
        cmoTilingComplexDirectedEdges_reverse_mem hs tiling hreverseComplex
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

theorem cmoSelected_sources_subset_terminal
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    edgeSourceFinset
        (cmoReducedRightmostSkeleton hs tiling).selectedEdgePairs ⊆
      edgeSourceFinset (cmoReducedRightmostTerminal hs tiling).edges := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  rw [← hsource]
  exact cmoSelectedPair_source_mem_terminal hs tiling hedge

theorem cmoTerminal_source_eq_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    edgeSourceFinset (cmoReducedRightmostTerminal hs tiling).edges =
      cmoTilingBoundaryVertexFinset tiling := by
  apply Finset.Subset.antisymm
  · exact cmoTerminal_source_subset_boundaryVertices hs tiling
  · have hsource := edgeSourceFinset_perm
      (cmoTerminal_edgeAccounting_perm hs tiling)
    rw [cmoEdgeSourceFinset_tilingComplex hs tiling,
      edgeSourceFinset_append] at hsource
    rw [hsource]
    exact Finset.union_subset Finset.Subset.rfl
      (cmoSelected_sources_subset_terminal hs tiling)

end FiniteDefects
