import D4KernelOnly.D4TilingVertices
import BenzelProblem6Kernel.SelectedSpliceEndpointSupport

/-! # Exact edge and vertex accounting at the d=4 peeling terminal -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 800000

theorem d4Terminal_edgeAccounting_perm {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List.Perm (d4TilingComplexDirectedEdges tiling)
      ((d4ReducedRightmostTerminal tiling).edges ++
        (d4ReducedRightmostSkeleton tiling).selectedEdgePairs) := by
  let skeleton := d4ReducedRightmostSkeleton tiling
  have hreverse : List.Perm
      (reverseLiteralPlacementBoundaryList
        (d4ShadowPlacementFinset tiling).toList)
      skeleton.reverseTileBoundaries :=
    skeleton.reverseTileBoundaries_perm_initial.symm
  have hinitial : List.Perm
      (d4ReducedBoundaryWalk m ++
        reverseLiteralPlacementBoundaryList
          (d4ShadowPlacementFinset tiling).toList)
      (d4ReducedBoundaryWalk m ++ skeleton.reverseTileBoundaries) :=
    hreverse.append_left _
  exact hinitial.trans skeleton.edge_accounting_perm

theorem d4Terminal_append_selected_nodup {m : ℕ}
    (tiling : D4LiteralTiling m) :
    ((d4ReducedRightmostTerminal tiling).edges ++
      (d4ReducedRightmostSkeleton tiling).selectedEdgePairs).Nodup :=
  (d4TilingComplexDirectedEdges_nodup tiling).perm
    (d4Terminal_edgeAccounting_perm tiling)

theorem d4ReducedRightmostTerminal_nodup {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ReducedRightmostTerminal tiling).edges.Nodup :=
  (List.nodup_append.mp (d4Terminal_append_selected_nodup tiling)).1

theorem d4Terminal_disjoint_selected {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List.Disjoint (d4ReducedRightmostTerminal tiling).edges
      (d4ReducedRightmostSkeleton tiling).selectedEdgePairs :=
  (List.nodup_append.mp (d4Terminal_append_selected_nodup tiling)).2.2

theorem d4ReducedRightmostTerminal_reverse_mem {m : ℕ}
    (tiling : D4LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ (d4ReducedRightmostTerminal tiling).edges) :
    reverseLabeledHexEdge edge ∈
      (d4ReducedRightmostTerminal tiling).edges := by
  let skeleton := d4ReducedRightmostSkeleton tiling
  have haccount := d4Terminal_edgeAccounting_perm tiling
  have hedgeComplex : edge ∈ d4TilingComplexDirectedEdges tiling :=
    haccount.mem_iff.mpr (List.mem_append_left _ hedge)
  have hreverseComplex :=
    d4TilingComplexDirectedEdges_reverse_mem tiling hedgeComplex
  have hsplit : reverseLabeledHexEdge edge ∈
      (d4ReducedRightmostTerminal tiling).edges ++
        skeleton.selectedEdgePairs := haccount.mem_iff.mp hreverseComplex
  rw [List.mem_append] at hsplit
  rcases hsplit with hterminal | hselected
  · exact hterminal
  · have hedgeSelected : edge ∈ skeleton.selectedEdgePairs := by
      simpa [reverseLabeledHexEdge_involutive] using
        skeleton.selectedEdgePairs_reverse_mem hselected
    exact (List.disjoint_left.mp (d4Terminal_disjoint_selected tiling))
      hedge hedgeSelected |>.elim

theorem d4Terminal_length_identity {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ReducedRightmostTerminal tiling).edges.length +
        2 * d4KernelRightStoneCount tiling =
      12 * m + 24 +
        12 * (d4ShadowPlacementFinset tiling).card := by
  have hlength := (d4Terminal_edgeAccounting_perm tiling).length_eq
  rw [d4TilingComplexDirectedEdges, List.length_append,
    d4ReducedBoundary_length, List.length_append,
    (d4ReducedRightmostSkeleton tiling).selectedEdgePairs_length] at hlength
  have hreverse := reverseD4PlacementBoundary_length_identity tiling
  omega

theorem d4Terminal_length_add_two_eq_twice_boundary_vertices {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ReducedRightmostTerminal tiling).edges.length + 2 =
      2 * (d4TilingBoundaryVertexFinset tiling).card := by
  have hterminal := d4Terminal_length_identity tiling
  have hvertices := d4BoundaryVertex_card_add_stones tiling
  have hglobal := d4TilePerimeterVertex_identity tiling
  omega

theorem d4ReversePlacement_source_eq_boundaryVertices {m : ℕ}
    (tiling : D4LiteralTiling m) :
    edgeSourceFinset
        (reverseLiteralPlacementBoundaryList
          (d4ShadowPlacementFinset tiling).toList) =
      d4TilingBoundaryVertexFinset tiling := by
  rw [edgeSourceFinset_reversePlacementList,
    d4TilingBoundaryVertexFinset]
  congr 1
  ext placement
  simp

theorem d4Outer_edge_mem_some_placement {m : ℕ}
    (tiling : D4LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ d4ReducedBoundaryWalk m) :
    ∃ placement ∈ d4ShadowPlacementFinset tiling,
      edge ∈ literalPlacementBoundary placement := by
  have hcoefficient : directedEdgeCoefficient
      (literalPlacementBoundaryList
        (d4ShadowPlacementFinset tiling).toList) edge = 1 := by
    rw [← d4ReducedBoundary_same_placement_chain tiling edge]
    exact d4PerimeterEdge_coefficient_one m
      ((d4PerimeterEdges_perm_reduced m).mem_iff.mpr hedge)
  have hedgeList := edge_mem_of_directedEdgeCoefficient_eq_one
    _ edge hcoefficient
  rw [literalPlacementBoundaryList, List.mem_flatMap] at hedgeList
  obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeList
  exact ⟨placement, Finset.mem_toList.mp hplacement, hedgePlacement⟩

theorem d4Outer_source_subset_boundaryVertices {m : ℕ}
    (tiling : D4LiteralTiling m) :
    edgeSourceFinset (d4ReducedBoundaryWalk m) ⊆
      d4TilingBoundaryVertexFinset tiling := by
  intro vertex hvertex
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  obtain ⟨placement, hplacement, hedgePlacement⟩ :=
    d4Outer_edge_mem_some_placement tiling hedge
  rw [d4TilingBoundaryVertexFinset, Finset.mem_biUnion]
  refine ⟨placement, hplacement, ?_⟩
  simp only [placementBoundaryVertexFinset,
    prototypeBoundaryVertexFinset, edgeSourceFinset,
    List.mem_toFinset, List.mem_map]
  exact ⟨edge, hedgePlacement, hsource⟩

theorem d4EdgeSourceFinset_tilingComplex {m : ℕ}
    (tiling : D4LiteralTiling m) :
    edgeSourceFinset (d4TilingComplexDirectedEdges tiling) =
      d4TilingBoundaryVertexFinset tiling := by
  rw [d4TilingComplexDirectedEdges, edgeSourceFinset_append,
    d4ReversePlacement_source_eq_boundaryVertices]
  exact Finset.union_eq_right.mpr (d4Outer_source_subset_boundaryVertices tiling)

theorem d4Terminal_source_subset_boundaryVertices {m : ℕ}
    (tiling : D4LiteralTiling m) :
    edgeSourceFinset (d4ReducedRightmostTerminal tiling).edges ⊆
      d4TilingBoundaryVertexFinset tiling := by
  have hsource := edgeSourceFinset_perm (d4Terminal_edgeAccounting_perm tiling)
  rw [d4EdgeSourceFinset_tilingComplex, edgeSourceFinset_append] at hsource
  rw [hsource]
  exact Finset.subset_union_left

end FiniteDefects
