import D4KernelOnly.GeneralOffsetTilingVertices
import BenzelProblem6Kernel.SelectedSpliceEndpointSupport

/-! # Edge, vertex, and source accounting at the class-zero terminal -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czTerminal_edgeAccounting_perm
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    List.Perm (czTilingComplexDirectedEdges hs hr tiling)
      ((czReducedRightmostTerminal hs hr tiling).edges ++
        (czReducedRightmostSkeleton hs hr tiling).selectedEdgePairs) := by
  let skeleton := czReducedRightmostSkeleton hs hr tiling
  have hreverse : List.Perm
      (reverseLiteralPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList)
      skeleton.reverseTileBoundaries :=
    skeleton.reverseTileBoundaries_perm_initial.symm
  have hinitial : List.Perm
      (czReducedBoundaryWalk s r ++
        reverseLiteralPlacementBoundaryList
          (offsetShadowPlacementFinset tiling).toList)
      (czReducedBoundaryWalk s r ++ skeleton.reverseTileBoundaries) :=
    hreverse.append_left _
  exact hinitial.trans skeleton.edge_accounting_perm

theorem czTerminal_append_selected_nodup
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    ((czReducedRightmostTerminal hs hr tiling).edges ++
      (czReducedRightmostSkeleton hs hr tiling).selectedEdgePairs).Nodup :=
  (czTilingComplexDirectedEdges_nodup hs hr tiling).perm
    (czTerminal_edgeAccounting_perm hs hr tiling)

theorem czReducedRightmostTerminal_nodup
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czReducedRightmostTerminal hs hr tiling).edges.Nodup :=
  (List.nodup_append.mp (czTerminal_append_selected_nodup hs hr tiling)).1

theorem czTerminal_disjoint_selected
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    List.Disjoint (czReducedRightmostTerminal hs hr tiling).edges
      (czReducedRightmostSkeleton hs hr tiling).selectedEdgePairs :=
  (List.nodup_append.mp (czTerminal_append_selected_nodup hs hr tiling)).2.2

theorem czReducedRightmostTerminal_reverse_mem
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) {edge : LabeledHexEdge}
    (hedge : edge ∈ (czReducedRightmostTerminal hs hr tiling).edges) :
    reverseLabeledHexEdge edge ∈
      (czReducedRightmostTerminal hs hr tiling).edges := by
  let skeleton := czReducedRightmostSkeleton hs hr tiling
  have haccount := czTerminal_edgeAccounting_perm hs hr tiling
  have hedgeComplex : edge ∈ czTilingComplexDirectedEdges hs hr tiling :=
    haccount.mem_iff.mpr (List.mem_append_left _ hedge)
  have hreverseComplex :=
    czTilingComplexDirectedEdges_reverse_mem hs hr tiling hedgeComplex
  have hsplit : reverseLabeledHexEdge edge ∈
      (czReducedRightmostTerminal hs hr tiling).edges ++ skeleton.selectedEdgePairs :=
    haccount.mem_iff.mp hreverseComplex
  rw [List.mem_append] at hsplit
  rcases hsplit with ht | hselected
  · exact ht
  · have hedgeSelected : edge ∈ skeleton.selectedEdgePairs := by
      simpa [reverseLabeledHexEdge_involutive] using
        skeleton.selectedEdgePairs_reverse_mem hselected
    exact (List.disjoint_left.mp (czTerminal_disjoint_selected hs hr tiling))
      hedge hedgeSelected |>.elim

theorem czTerminal_length_identity
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czReducedRightmostTerminal hs hr tiling).edges.length +
        2 * offsetLiteralStoneCount tiling =
      (12 * (s + r) - 6) +
        12 * (offsetShadowPlacementFinset tiling).card := by
  have hlength := (czTerminal_edgeAccounting_perm hs hr tiling).length_eq
  rw [czTilingComplexDirectedEdges, List.length_append,
    czReducedBoundary_length s r hs hr, List.length_append,
    (czReducedRightmostSkeleton hs hr tiling).selectedEdgePairs_length] at hlength
  have hreverse := reverseOffsetPlacementBoundary_length_identity tiling
  omega

theorem czTerminal_length_add_two_eq_twice_boundary_vertices
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czReducedRightmostTerminal hs hr tiling).edges.length + 2 =
      2 * (offsetTilingBoundaryVertexFinset tiling).card := by
  have hterminal := czTerminal_length_identity hs hr tiling
  have hvertices := offsetBoundaryVertex_card_add_stones tiling
  have hglobal := czTilePerimeterVertexKernelOnly s r hs hr tiling
  rw [offsetShadowPlacementFinset_card] at hterminal
  omega

theorem czReversePlacement_source_eq_boundaryVertices
    {s r : ℕ} (tiling : CZLiteralTiling s r) :
    edgeSourceFinset
        (reverseLiteralPlacementBoundaryList
          (offsetShadowPlacementFinset tiling).toList) =
      offsetTilingBoundaryVertexFinset tiling := by
  rw [edgeSourceFinset_reversePlacementList,
    offsetTilingBoundaryVertexFinset]
  congr 1
  ext placement
  simp

theorem czOuter_edge_mem_some_placement
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) {edge : LabeledHexEdge}
    (hedge : edge ∈ czReducedBoundaryWalk s r) :
    ∃ placement ∈ offsetShadowPlacementFinset tiling,
      edge ∈ literalPlacementBoundary placement := by
  have hcoefficient : directedEdgeCoefficient
      (literalPlacementBoundaryList (offsetShadowPlacementFinset tiling).toList)
      edge = 1 := by
    rw [← czReducedBoundary_same_placement_chain hs hr tiling edge]
    exact czPerimeterEdge_coefficient_one s r hs hr
      ((czPerimeterEdges_perm_reduced s r hs hr).mem_iff.mpr hedge)
  have hedgeList := edge_mem_of_directedEdgeCoefficient_eq_one _ edge hcoefficient
  rw [literalPlacementBoundaryList, List.mem_flatMap] at hedgeList
  obtain ⟨placement, hplacement, hpedge⟩ := hedgeList
  exact ⟨placement, Finset.mem_toList.mp hplacement, hpedge⟩

theorem czOuter_source_subset_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    edgeSourceFinset (czReducedBoundaryWalk s r) ⊆
      offsetTilingBoundaryVertexFinset tiling := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  obtain ⟨placement, hp, hedgePlacement⟩ :=
    czOuter_edge_mem_some_placement hs hr tiling hedge
  rw [offsetTilingBoundaryVertexFinset, Finset.mem_biUnion]
  refine ⟨placement, hp, ?_⟩
  simp only [placementBoundaryVertexFinset,
    prototypeBoundaryVertexFinset, edgeSourceFinset,
    List.mem_toFinset, List.mem_map]
  exact ⟨edge, hedgePlacement, hsource⟩

theorem czEdgeSourceFinset_tilingComplex
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    edgeSourceFinset (czTilingComplexDirectedEdges hs hr tiling) =
      offsetTilingBoundaryVertexFinset tiling := by
  rw [czTilingComplexDirectedEdges, edgeSourceFinset_append,
    czReversePlacement_source_eq_boundaryVertices]
  exact Finset.union_eq_right.mpr
    (czOuter_source_subset_boundaryVertices hs hr tiling)

theorem czTerminal_source_subset_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    edgeSourceFinset (czReducedRightmostTerminal hs hr tiling).edges ⊆
      offsetTilingBoundaryVertexFinset tiling := by
  have hsource := edgeSourceFinset_perm (czTerminal_edgeAccounting_perm hs hr tiling)
  rw [czEdgeSourceFinset_tilingComplex hs hr tiling,
    edgeSourceFinset_append] at hsource
  rw [hsource]
  exact Finset.subset_union_left

end FiniteDefects
