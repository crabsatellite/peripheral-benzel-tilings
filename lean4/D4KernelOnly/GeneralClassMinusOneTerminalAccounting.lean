import D4KernelOnly.GeneralClassMinusOneTilingVertices
import BenzelProblem6Kernel.SelectedSpliceEndpointSupport

/-! # Edge and vertex accounting at the class-minus-one peeling terminal -/

namespace FiniteDefects

open BenzelProblem6Kernel

def CMOTilePerimeterVertexStatement : Prop :=
  ∀ (s r : ℕ), 1 ≤ s → ∀ tiling : CMOLiteralTiling s r,
    12 * (offsetShadowPlacementFinset tiling).card +
        12 * (s + r) + 2 =
      2 * (offsetCellVertexFinset (2 * s + r - 1) (3 * s + 1)).card

theorem cmoTerminal_edgeAccounting_perm
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    List.Perm (cmoTilingComplexDirectedEdges hs tiling)
      ((cmoReducedRightmostTerminal hs tiling).edges ++
        (cmoReducedRightmostSkeleton hs tiling).selectedEdgePairs) := by
  let skeleton := cmoReducedRightmostSkeleton hs tiling
  have hreverse : List.Perm
      (reverseLiteralPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList)
      skeleton.reverseTileBoundaries :=
    skeleton.reverseTileBoundaries_perm_initial.symm
  have hinitial : List.Perm
      (cmoReducedBoundaryWalk s r ++
        reverseLiteralPlacementBoundaryList
          (offsetShadowPlacementFinset tiling).toList)
      (cmoReducedBoundaryWalk s r ++ skeleton.reverseTileBoundaries) :=
    hreverse.append_left _
  exact hinitial.trans skeleton.edge_accounting_perm

theorem cmoTerminal_append_selected_nodup
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    ((cmoReducedRightmostTerminal hs tiling).edges ++
      (cmoReducedRightmostSkeleton hs tiling).selectedEdgePairs).Nodup :=
  (cmoTilingComplexDirectedEdges_nodup hs tiling).perm
    (cmoTerminal_edgeAccounting_perm hs tiling)

theorem cmoReducedRightmostTerminal_nodup
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoReducedRightmostTerminal hs tiling).edges.Nodup :=
  (List.nodup_append.mp (cmoTerminal_append_selected_nodup hs tiling)).1

theorem cmoTerminal_disjoint_selected
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    List.Disjoint (cmoReducedRightmostTerminal hs tiling).edges
      (cmoReducedRightmostSkeleton hs tiling).selectedEdgePairs :=
  (List.nodup_append.mp (cmoTerminal_append_selected_nodup hs tiling)).2.2

theorem cmoReducedRightmostTerminal_reverse_mem
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ (cmoReducedRightmostTerminal hs tiling).edges) :
    reverseLabeledHexEdge edge ∈
      (cmoReducedRightmostTerminal hs tiling).edges := by
  let skeleton := cmoReducedRightmostSkeleton hs tiling
  have haccount := cmoTerminal_edgeAccounting_perm hs tiling
  have hedgeComplex : edge ∈ cmoTilingComplexDirectedEdges hs tiling :=
    haccount.mem_iff.mpr (List.mem_append_left _ hedge)
  have hreverseComplex :=
    cmoTilingComplexDirectedEdges_reverse_mem hs tiling hedgeComplex
  have hsplit : reverseLabeledHexEdge edge ∈
      (cmoReducedRightmostTerminal hs tiling).edges ++
        skeleton.selectedEdgePairs := haccount.mem_iff.mp hreverseComplex
  rw [List.mem_append] at hsplit
  rcases hsplit with hterminal | hselected
  · exact hterminal
  · have hedgeSelected : edge ∈ skeleton.selectedEdgePairs := by
      simpa [reverseLabeledHexEdge_involutive] using
        skeleton.selectedEdgePairs_reverse_mem hselected
    exact (List.disjoint_left.mp
      (cmoTerminal_disjoint_selected hs tiling)) hedge hedgeSelected |>.elim

theorem cmoTerminal_length_identity
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoReducedRightmostTerminal hs tiling).edges.length +
        2 * cmoLiteralRightStoneCount tiling =
      12 * (s + r) +
        12 * (offsetShadowPlacementFinset tiling).card := by
  have hlength := (cmoTerminal_edgeAccounting_perm hs tiling).length_eq
  rw [cmoTilingComplexDirectedEdges, List.length_append,
    cmoReducedBoundary_length s r hs, List.length_append,
    (cmoReducedRightmostSkeleton hs tiling).selectedEdgePairs_length] at hlength
  have hreverse := reverseCMOPlacementBoundary_length_identity tiling
  omega

theorem cmoTerminal_length_add_two_eq_twice_boundary_vertices
    (hEuler : CMOTilePerimeterVertexStatement)
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoReducedRightmostTerminal hs tiling).edges.length + 2 =
      2 * (cmoTilingBoundaryVertexFinset tiling).card := by
  have hterminal := cmoTerminal_length_identity hs tiling
  have hvertices := cmoBoundaryVertex_card_add_stones tiling
  have hglobal := hEuler s r hs tiling
  omega

end FiniteDefects
