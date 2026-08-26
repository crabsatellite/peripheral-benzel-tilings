import D4KernelOnly.GeneralClassMinusOneEuler

/-! # Source support of the class-minus-one terminal contour -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem cmoReversePlacement_source_eq_boundaryVertices
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    edgeSourceFinset
        (reverseLiteralPlacementBoundaryList
          (offsetShadowPlacementFinset tiling).toList) =
      cmoTilingBoundaryVertexFinset tiling := by
  rw [edgeSourceFinset_reversePlacementList,
    cmoTilingBoundaryVertexFinset]
  congr 1
  ext placement
  simp

theorem cmoOuter_edge_mem_some_placement
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {edge : LabeledHexEdge} (hedge : edge ∈ cmoReducedBoundaryWalk s r) :
    ∃ placement ∈ offsetShadowPlacementFinset tiling,
      edge ∈ literalPlacementBoundary placement := by
  have hcoefficient : directedEdgeCoefficient
      (literalPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList) edge = 1 := by
    rw [← cmoReducedBoundary_same_placement_chain hs tiling edge]
    exact cmoPerimeterEdge_coefficient_one s r hs
      ((cmoPerimeterEdges_perm_reduced s r hs).mem_iff.mpr hedge)
  have hedgeList := edge_mem_of_directedEdgeCoefficient_eq_one
    _ edge hcoefficient
  rw [literalPlacementBoundaryList, List.mem_flatMap] at hedgeList
  obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeList
  exact ⟨placement, Finset.mem_toList.mp hplacement, hedgePlacement⟩

theorem cmoOuter_source_subset_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    edgeSourceFinset (cmoReducedBoundaryWalk s r) ⊆
      cmoTilingBoundaryVertexFinset tiling := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  obtain ⟨placement, hplacement, hedgePlacement⟩ :=
    cmoOuter_edge_mem_some_placement hs tiling hedge
  rw [cmoTilingBoundaryVertexFinset, Finset.mem_biUnion]
  refine ⟨placement, hplacement, ?_⟩
  simp only [placementBoundaryVertexFinset,
    prototypeBoundaryVertexFinset, edgeSourceFinset,
    List.mem_toFinset, List.mem_map]
  exact ⟨edge, hedgePlacement, hsource⟩

theorem cmoEdgeSourceFinset_tilingComplex
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    edgeSourceFinset (cmoTilingComplexDirectedEdges hs tiling) =
      cmoTilingBoundaryVertexFinset tiling := by
  rw [cmoTilingComplexDirectedEdges, edgeSourceFinset_append,
    cmoReversePlacement_source_eq_boundaryVertices]
  exact Finset.union_eq_right.mpr
    (cmoOuter_source_subset_boundaryVertices hs tiling)

theorem cmoTerminal_source_subset_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    edgeSourceFinset (cmoReducedRightmostTerminal hs tiling).edges ⊆
      cmoTilingBoundaryVertexFinset tiling := by
  have hsource := edgeSourceFinset_perm
    (cmoTerminal_edgeAccounting_perm hs tiling)
  rw [cmoEdgeSourceFinset_tilingComplex hs tiling,
    edgeSourceFinset_append] at hsource
  rw [hsource]
  exact Finset.subset_union_left

end FiniteDefects
