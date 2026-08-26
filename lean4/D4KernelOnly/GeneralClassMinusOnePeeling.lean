import D4KernelOnly.GeneralClassMinusOneAlternation
import BenzelProblem6Kernel.RightmostPeelingSkeleton

/-! # Premise-free rightmost peeling for arbitrary class-minus-one benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

abbrev CMOLiteralTiling (s r : ℕ) :=
  OffsetLiteralTiling (2 * s + r - 1) (3 * s + 1)

theorem cmoShadowPlacementFinset_toList_perm
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    List.Perm (offsetShadowPlacementFinset tiling).toList
      (offsetShadowPlacementList tiling) := by
  classical
  apply (List.perm_ext_iff_of_nodup
    (Finset.nodup_toList _) (by
      unfold offsetShadowPlacementList
      exact (Finset.nodup_toList tiling.1).map
        offsetShadowPlacement_injective)).mpr
  intro placement
  rw [Finset.mem_toList]
  rw [mem_offsetShadowPlacementFinset_iff]
  simp only [offsetShadowPlacementList, List.mem_map, Finset.mem_toList]

theorem cmoShadowPlacementFinset_boundary_perm
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    List.Perm
      (literalPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList)
      (literalPlacementBoundaryList (offsetShadowPlacementList tiling)) := by
  exact (cmoShadowPlacementFinset_toList_perm tiling).map
    literalPlacementBoundary |>.flatten

theorem cmoShadowPlacementFinsetBoundaries_eq_cellBoundaries
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    SameOrientedBoundaryChain
      (literalPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList)
      (orientedCellBoundaryList
        (offsetCellValueList (2 * s + r - 1) (3 * s + 1))) :=
  (SameOrientedBoundaryChain.perm
    (cmoShadowPlacementFinset_boundary_perm tiling)).trans
      (offsetShadowPlacementBoundaries_eq_cellBoundaries tiling)

theorem cmoInitialRightmostBoundaryCoefficientInvariant
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    RightmostBoundaryCoefficientInvariant
      (classMinusOneLiteralBoundaryWalk s r)
      (offsetShadowPlacementFinset tiling) := by
  intro cell
  exact (directedEdgeCoefficient_classMinusOneBoundary_sideFive
      s r hs cell).trans
    ((cmoShadowPlacementFinsetBoundaries_eq_cellBoundaries tiling
      (cellBoundaryEdgeAt cell .side₅)).symm)

theorem cmoShadowPlacement_unique_of_cell
    {s r : ℕ} (tiling : CMOLiteralTiling s r)
    {left right : LiteralPlacement (2 * s + r - 1)}
    (hleft : left ∈ offsetShadowPlacementFinset tiling)
    (hright : right ∈ offsetShadowPlacementFinset tiling)
    {cell : Cell} (hcellLeft : cell ∈ left.cells)
    (hcellRight : cell ∈ right.cells) : left = right := by
  obtain ⟨leftSource, hleftSource, hleftEq⟩ :=
    (mem_offsetShadowPlacementFinset_iff tiling left).1 hleft
  obtain ⟨rightSource, hrightSource, hrightEq⟩ :=
    (mem_offsetShadowPlacementFinset_iff tiling right).1 hright
  subst left
  subst right
  rw [offsetShadowPlacement_cells] at hcellLeft hcellRight
  let regionCell : OffsetCell (2 * s + r - 1) (3 * s + 1) :=
    ⟨cell, leftSource.2 cell hcellLeft⟩
  obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
  have hleftUnique : leftSource = covering :=
    hunique leftSource ⟨hleftSource, hcellLeft⟩
  have hrightUnique : rightSource = covering :=
    hunique rightSource ⟨hrightSource, hcellRight⟩
  exact congrArg offsetShadowPlacement
    (hleftUnique.trans hrightUnique.symm)

theorem cmoShadowSubfamily_flattened_cells_nodup
    {s r : ℕ} (tiling : CMOLiteralTiling s r)
    (placements : Finset (LiteralPlacement (2 * s + r - 1)))
    (hsubset : placements ⊆ offsetShadowPlacementFinset tiling) :
    (placements.toList.flatMap LiteralPlacement.cells).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact BenzelProblem6Kernel.placementCellList_nodup placement.1
  · apply (Finset.nodup_toList placements).pairwise_of_forall_ne
    intro left hleft right hright hne
    change List.Disjoint left.cells right.cells
    rw [List.disjoint_left]
    intro cell hcellLeft hcellRight
    exact hne (cmoShadowPlacement_unique_of_cell tiling
      (hsubset (Finset.mem_toList.mp hleft))
      (hsubset (Finset.mem_toList.mp hright)) hcellLeft hcellRight)

theorem cmoExposed_edge_placementBoundaryList_coefficient_one
    {s r : ℕ} (tiling : CMOLiteralTiling s r)
    (placements : Finset (LiteralPlacement (2 * s + r - 1)))
    (hsubset : placements ⊆ offsetShadowPlacementFinset tiling)
    {placement : LiteralPlacement (2 * s + r - 1)}
    (hplacement : placement ∈ placements)
    {cell : Cell} (hcell : cell ∈ placement.cells)
    (hneighbor : neighboringCell cell .side₅ ∉
      placementUnionCells placements) :
    directedEdgeCoefficient
        (literalPlacementBoundaryList placements.toList)
        (cellBoundaryEdgeAt cell .side₅) = 1 := by
  let cells := placements.toList.flatMap LiteralPlacement.cells
  have hnodup : cells.Nodup :=
    cmoShadowSubfamily_flattened_cells_nodup tiling placements hsubset
  have hcellMem : cell ∈ cells := by
    change cell ∈ placements.toList.flatMap LiteralPlacement.cells
    rw [List.mem_flatMap]
    exact ⟨placement, Finset.mem_toList.mpr hplacement, hcell⟩
  have hneighborMem : neighboringCell cell .side₅ ∉ cells := by
    intro hmem
    change neighboringCell cell .side₅ ∈
      placements.toList.flatMap LiteralPlacement.cells at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨owner, howner, hownerCell⟩ := hmem
    apply hneighbor
    rw [placementUnionCells, Finset.mem_biUnion]
    exact ⟨owner, Finset.mem_toList.mp howner,
      List.mem_toFinset.mpr hownerCell⟩
  have hcellCount := lawful_count_eq_indicator_of_nodup
    cells hnodup cell
  have hneighborCount := lawful_count_eq_indicator_of_nodup
    cells hnodup (neighboringCell cell .side₅)
  have hgrouped := orientedCellBoundaryList_flatMap_placements placements.toList
  have hcoefficient := hgrouped (cellBoundaryEdgeAt cell .side₅)
  rw [directedEdgeCoefficient_orientedCellBoundaryList,
    hcellCount, hneighborCount] at hcoefficient
  simpa [hcellMem, hneighborMem] using hcoefficient.symm

theorem cmoCurrentRightmostExposedEdge_nonempty
    {s r : ℕ} (tiling : CMOLiteralTiling s r)
    (placements : Finset (LiteralPlacement (2 * s + r - 1)))
    (hsubset : placements ⊆ offsetShadowPlacementFinset tiling)
    (hplacements : placements.Nonempty)
    (boundary : List LabeledHexEdge)
    (hinvariant : RightmostBoundaryCoefficientInvariant boundary placements) :
    Nonempty (CurrentRightmostExposedEdge placements boundary) := by
  obtain ⟨placement, hplacement, cell, hcell,
      hneighbor, hedgePlacement⟩ :=
    exists_rightmost_exposed_placement hplacements
  have hplacementCoefficient :=
    cmoExposed_edge_placementBoundaryList_coefficient_one
      tiling placements hsubset hplacement hcell hneighbor
  have hboundaryCoefficient :
      directedEdgeCoefficient boundary
        (cellBoundaryEdgeAt cell .side₅) = 1 := by
    rw [hinvariant cell]
    exact hplacementCoefficient
  have hedgeBoundary := edge_mem_of_directedEdgeCoefficient_eq_one
    boundary (cellBoundaryEdgeAt cell .side₅) hboundaryCoefficient
  exact ⟨⟨placement, hplacement, cell, hcell,
    hneighbor, hedgePlacement, hedgeBoundary⟩⟩

noncomputable def buildCMORightmostPeelingSkeleton
    {s r : ℕ} (tiling : CMOLiteralTiling s r)
    (region : RootedAlternatingBoundary)
    (placements : Finset (LiteralPlacement (2 * s + r - 1)))
    (hsubset : placements ⊆ offsetShadowPlacementFinset tiling)
    (hinvariant : RightmostBoundaryCoefficientInvariant
      region.edges placements) :
    RightmostPeelingSkeleton (2 * s + r - 1) region placements := by
  classical
  by_cases hempty : placements = ∅
  · subst placements
    exact .done region
  · have hnonempty : placements.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let candidate := Classical.choice
      (cmoCurrentRightmostExposedEdge_nonempty tiling placements
        hsubset hnonempty region.edges hinvariant)
    let edge := cellBoundaryEdgeAt candidate.cell .side₅
    let available := Classical.choice
      (availableGeometricTileSplice_nonempty region candidate.placement edge
        candidate.boundary_edge_mem candidate.placement_edge_mem)
    let splice := available.splice
    have hboundary : splice.boundary = region.edges := available.boundary_exact
    have hsplicePlacement : splice.placement = candidate.placement :=
      available.placement_exact
    have hplacement' : splice.placement ∈ placements := by
      rw [hsplicePlacement]
      exact candidate.placement_mem
    have hcell' : candidate.cell ∈ splice.placement.cells := by
      rw [hsplicePlacement]
      exact candidate.cell_mem
    have hcellNotRemaining : candidate.cell ∉
        placementUnionCells (placements.erase splice.placement) := by
      intro hremaining
      rw [placementUnionCells, Finset.mem_biUnion] at hremaining
      obtain ⟨other, hother, hotherCell⟩ := hremaining
      have hotherMem : other ∈ placements := Finset.mem_of_mem_erase hother
      have hsame : splice.placement = other :=
        cmoShadowPlacement_unique_of_cell tiling
          (hsubset hplacement') (hsubset hotherMem)
          hcell' (List.mem_toFinset.mp hotherCell)
      exact (Finset.mem_erase.mp hother).1 hsame.symm
    have hsubset' : placements.erase splice.placement ⊆
        offsetShadowPlacementFinset tiling := by
      intro placement hplacement
      exact hsubset (Finset.mem_of_mem_erase hplacement)
    have hinvariant' : RightmostBoundaryCoefficientInvariant
        (region.spliceRemaining splice hboundary).edges
        (placements.erase splice.placement) := by
      change RightmostBoundaryCoefficientInvariant splice.remainingBoundary _
      exact rightmostBoundaryInvariant_after_raw_splice
        hinvariant splice hboundary hplacement'
    exact .peel region placements splice hboundary hplacement'
      candidate.cell hcell' available.edge_exact candidate.neighbor_outside
      hcellNotRemaining
      (buildCMORightmostPeelingSkeleton tiling
        (region.spliceRemaining splice hboundary)
        (placements.erase splice.placement) hsubset' hinvariant')
termination_by placements.card
decreasing_by
  exact Finset.card_erase_lt_of_mem hplacement'

noncomputable def cmoRightmostSkeleton
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    RightmostPeelingSkeleton (2 * s + r - 1)
      (classMinusOneLiteralRootedBoundary s r)
      (offsetShadowPlacementFinset tiling) :=
  buildCMORightmostPeelingSkeleton tiling
    (classMinusOneLiteralRootedBoundary s r)
    (offsetShadowPlacementFinset tiling) (fun _ h => h)
    (cmoInitialRightmostBoundaryCoefficientInvariant hs tiling)

noncomputable def cmoRightmostTerminal
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    RootedAlternatingBoundary :=
  (cmoRightmostSkeleton hs tiling).terminalRegion

end FiniteDefects
