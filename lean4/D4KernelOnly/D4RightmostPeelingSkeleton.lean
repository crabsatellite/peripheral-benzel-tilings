import D4KernelOnly.D4InitialPeelingBoundary
import BenzelProblem6Kernel.RightmostPeelingSkeleton

/-! # The premise-free rightmost peeling skeleton for d=4 tilings -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem d4ShadowPlacement_unique_of_cell {m : ℕ}
    (tiling : D4LiteralTiling m)
    {left right : LiteralPlacement m}
    (hleft : left ∈ d4ShadowPlacementFinset tiling)
    (hright : right ∈ d4ShadowPlacementFinset tiling)
    {cell : Cell} (hcellLeft : cell ∈ left.cells)
    (hcellRight : cell ∈ right.cells) :
    left = right := by
  obtain ⟨leftSource, hleftSource, hleftEq⟩ :=
    (mem_d4ShadowPlacementFinset_iff tiling left).1 hleft
  obtain ⟨rightSource, hrightSource, hrightEq⟩ :=
    (mem_d4ShadowPlacementFinset_iff tiling right).1 hright
  subst left
  subst right
  rw [d4ShadowPlacement_cells] at hcellLeft hcellRight
  let regionCell : D4Cell m :=
    ⟨cell, leftSource.2 cell hcellLeft⟩
  obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
  have hleftUnique : leftSource = covering :=
    hunique leftSource ⟨hleftSource, hcellLeft⟩
  have hrightUnique : rightSource = covering :=
    hunique rightSource ⟨hrightSource, hcellRight⟩
  exact congrArg d4ShadowPlacement
    (hleftUnique.trans hrightUnique.symm)

theorem d4Exposed_edge_placementBoundaryList_coefficient_one {m : ℕ}
    (tiling : D4LiteralTiling m)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ d4ShadowPlacementFinset tiling)
    {placement : LiteralPlacement m} (hplacement : placement ∈ placements)
    {cell : Cell} (hcell : cell ∈ placement.cells)
    (hneighbor : neighboringCell cell .side₅ ∉
      placementUnionCells placements) :
    directedEdgeCoefficient
        (literalPlacementBoundaryList placements.toList)
        (cellBoundaryEdgeAt cell .side₅) = 1 := by
  let cells := placements.toList.flatMap LiteralPlacement.cells
  have hnodup : cells.Nodup :=
    d4ShadowSubfamily_flattened_cells_nodup tiling placements hsubset
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
  have hgrouped := orientedCellBoundaryList_flatMap_placements
    placements.toList
  have hcoefficient := hgrouped (cellBoundaryEdgeAt cell .side₅)
  rw [directedEdgeCoefficient_orientedCellBoundaryList,
    hcellCount, hneighborCount] at hcoefficient
  simpa [hcellMem, hneighborMem] using hcoefficient.symm

theorem d4CurrentRightmostExposedEdge_nonempty {m : ℕ}
    (tiling : D4LiteralTiling m)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ d4ShadowPlacementFinset tiling)
    (hplacements : placements.Nonempty)
    (boundary : List LabeledHexEdge)
    (hinvariant : RightmostBoundaryCoefficientInvariant boundary placements) :
    Nonempty (CurrentRightmostExposedEdge placements boundary) := by
  obtain ⟨placement, hplacement, cell, hcell,
      hneighbor, hedgePlacement⟩ :=
    exists_rightmost_exposed_placement hplacements
  have hplacementCoefficient :=
    d4Exposed_edge_placementBoundaryList_coefficient_one
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

noncomputable def buildD4RightmostPeelingSkeleton {m : ℕ}
    (tiling : D4LiteralTiling m)
    (region : RootedAlternatingBoundary)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ d4ShadowPlacementFinset tiling)
    (hinvariant : RightmostBoundaryCoefficientInvariant
      region.edges placements) :
    RightmostPeelingSkeleton m region placements := by
  classical
  by_cases hempty : placements = ∅
  · subst placements
    exact .done region
  · have hnonempty : placements.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let candidate := Classical.choice
      (d4CurrentRightmostExposedEdge_nonempty tiling placements
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
        d4ShadowPlacement_unique_of_cell tiling
          (hsubset hplacement') (hsubset hotherMem)
          hcell' (List.mem_toFinset.mp hotherCell)
      exact (Finset.mem_erase.mp hother).1 hsame.symm
    have hsubset' : placements.erase splice.placement ⊆
        d4ShadowPlacementFinset tiling := by
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
      (buildD4RightmostPeelingSkeleton tiling
        (region.spliceRemaining splice hboundary)
        (placements.erase splice.placement) hsubset' hinvariant')
termination_by placements.card
decreasing_by
  exact Finset.card_erase_lt_of_mem hplacement'

noncomputable def d4RightmostSkeleton {m : ℕ}
    (tiling : D4LiteralTiling m) :
    RightmostPeelingSkeleton m
      (d4LiteralRootedBoundary m) (d4ShadowPlacementFinset tiling) :=
  buildD4RightmostPeelingSkeleton tiling
    (d4LiteralRootedBoundary m) (d4ShadowPlacementFinset tiling)
    (fun _ h => h) (d4InitialRightmostBoundaryCoefficientInvariant tiling)

noncomputable def d4RightmostTerminal {m : ℕ}
    (tiling : D4LiteralTiling m) : RootedAlternatingBoundary :=
  (d4RightmostSkeleton tiling).terminalRegion

end FiniteDefects
