import BenzelProblem6Kernel.GeometricSpliceOrientedChain

/-! # The rightmost-edge coefficient invariant for every remaining subfamily -/

namespace BenzelProblem6Kernel

def RightmostBoundaryCoefficientInvariant {m : ℕ}
    (boundary : List LabeledHexEdge)
    (placements : Finset (LiteralPlacement m)) : Prop :=
  ∀ cell : Cell,
    directedEdgeCoefficient boundary (cellBoundaryEdgeAt cell .side₅) =
      directedEdgeCoefficient
        (literalPlacementBoundaryList placements.toList)
        (cellBoundaryEdgeAt cell .side₅)

theorem initialRightmostBoundaryCoefficientInvariant
    {m : ℕ} (tiling : LiteralTiling m) :
    RightmostBoundaryCoefficientInvariant
      (literalReducedPeripheralBoundary m) tiling.1 := by
  intro cell
  exact literalReducedBoundary_eq_tilingBoundaryCoefficient_side₅
    tiling cell

theorem subfamily_flattened_cells_nodup {m : ℕ}
    (tiling : LiteralTiling m)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ tiling.1) :
    (placements.toList.flatMap LiteralPlacement.cells).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact placementCellList_nodup placement.1
  · apply (Finset.nodup_toList placements).pairwise_of_forall_ne
    intro left hleft right hright hne
    change List.Disjoint left.cells right.cells
    rw [List.disjoint_left]
    intro cell hcellLeft hcellRight
    have hleftTiling := hsubset (Finset.mem_toList.mp hleft)
    have hrightTiling := hsubset (Finset.mem_toList.mp hright)
    let regionCell : BenzelCell (m + 5) :=
      ⟨cell, left.2 cell hcellLeft⟩
    obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
    have hleftUnique : left = covering := hunique left
      ⟨hleftTiling, hcellLeft⟩
    have hrightUnique : right = covering := hunique right
      ⟨hrightTiling, hcellRight⟩
    exact hne (hleftUnique.trans hrightUnique.symm)

theorem finset_toList_perm_cons_erase {Alpha : Type*}
    [DecidableEq Alpha] (items : Finset Alpha) {item : Alpha}
    (hitem : item ∈ items) :
    List.Perm items.toList (item :: (items.erase item).toList) := by
  apply (List.perm_ext_iff_of_nodup
    (Finset.nodup_toList items) (by
      rw [List.nodup_cons]
      exact ⟨by simp, Finset.nodup_toList (items.erase item)⟩)).mpr
  intro candidate
  simp only [Finset.mem_toList, List.mem_cons, Finset.mem_erase]
  constructor
  · intro hcandidate
    by_cases heq : item = candidate
    · exact Or.inl heq.symm
    · exact Or.inr ⟨Ne.symm heq, hcandidate⟩
  · rintro (rfl | ⟨hne, hcandidate⟩)
    · exact hitem
    · exact hcandidate

theorem placementBoundaryList_erase_coefficient {m : ℕ}
    (placements : Finset (LiteralPlacement m))
    {placement : LiteralPlacement m} (hplacement : placement ∈ placements)
    (edge : LabeledHexEdge) :
    directedEdgeCoefficient
        (literalPlacementBoundaryList placements.toList) edge =
      directedEdgeCoefficient (literalPlacementBoundary placement) edge +
        directedEdgeCoefficient
          (literalPlacementBoundaryList (placements.erase placement).toList) edge := by
  have hperm := finset_toList_perm_cons_erase placements hplacement
  have hedgePerm : List.Perm
      (literalPlacementBoundaryList placements.toList)
      (literalPlacementBoundary placement ++
        literalPlacementBoundaryList (placements.erase placement).toList) := by
    simpa [literalPlacementBoundaryList, List.flatMap] using
      (hperm.map literalPlacementBoundary).flatten
  rw [(SameOrientedBoundaryChain.perm hedgePerm) edge,
    directedEdgeCoefficient_append]

theorem rightmostBoundaryInvariant_after_splice {m : ℕ}
    {boundary : List LabeledHexEdge}
    {placements : Finset (LiteralPlacement m)}
    (hinvariant : RightmostBoundaryCoefficientInvariant boundary placements)
    (splice : GeometricTileBoundarySplice m)
    (hboundary : splice.boundary = boundary)
    (hplacement : splice.placement ∈ placements) :
    RightmostBoundaryCoefficientInvariant
      (reduceGeometricBacktracks splice.remainingBoundary)
      (placements.erase splice.placement) := by
  intro cell
  rw [geometricTileBoundarySplice_reduced_coefficient]
  rw [hboundary, hinvariant cell,
    placementBoundaryList_erase_coefficient placements hplacement]
  ring

theorem rightmostBoundaryInvariant_after_raw_splice {m : ℕ}
    {boundary : List LabeledHexEdge}
    {placements : Finset (LiteralPlacement m)}
    (hinvariant : RightmostBoundaryCoefficientInvariant boundary placements)
    (splice : GeometricTileBoundarySplice m)
    (hboundary : splice.boundary = boundary)
    (hplacement : splice.placement ∈ placements) :
    RightmostBoundaryCoefficientInvariant splice.remainingBoundary
      (placements.erase splice.placement) := by
  intro cell
  rw [geometricTileBoundarySplice_remaining_coefficient]
  rw [hboundary, hinvariant cell,
    placementBoundaryList_erase_coefficient placements hplacement]
  ring

theorem exposed_edge_placementBoundaryList_coefficient_one {m : ℕ}
    (tiling : LiteralTiling m)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ tiling.1)
    {placement : LiteralPlacement m} (hplacement : placement ∈ placements)
    {cell : Cell} (hcell : cell ∈ placement.cells)
    (hneighbor : neighboringCell cell .side₅ ∉
      placementUnionCells placements) :
    directedEdgeCoefficient
        (literalPlacementBoundaryList placements.toList)
        (cellBoundaryEdgeAt cell .side₅) = 1 := by
  let cells := placements.toList.flatMap LiteralPlacement.cells
  have hnodup : cells.Nodup :=
    subfamily_flattened_cells_nodup tiling placements hsubset
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

theorem edge_mem_of_directedEdgeCoefficient_eq_one
    (boundary : List LabeledHexEdge) (edge : LabeledHexEdge)
    (hcoefficient : directedEdgeCoefficient boundary edge = 1) :
    edge ∈ boundary := by
  by_contra hnot
  have hzero := List.count_eq_zero.mpr hnot
  rw [directedEdgeCoefficient, hzero] at hcoefficient
  omega

theorem exists_current_rightmost_exposed_edge {m : ℕ}
    (tiling : LiteralTiling m)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ tiling.1)
    (hplacements : placements.Nonempty)
    (boundary : List LabeledHexEdge)
    (hinvariant : RightmostBoundaryCoefficientInvariant boundary placements) :
    ∃ placement ∈ placements, ∃ cell ∈ placement.cells,
      let edge := cellBoundaryEdgeAt cell .side₅
      edge ∈ literalPlacementBoundary placement ∧ edge ∈ boundary := by
  obtain ⟨placement, hplacement, cell, hcell,
      hneighbor, hedgePlacement⟩ :=
    exists_rightmost_exposed_placement hplacements
  have hplacementCoefficient :=
    exposed_edge_placementBoundaryList_coefficient_one
      tiling placements hsubset hplacement hcell hneighbor
  have hboundaryCoefficient :
      directedEdgeCoefficient boundary
        (cellBoundaryEdgeAt cell .side₅) = 1 := by
    rw [hinvariant cell]
    exact hplacementCoefficient
  exact ⟨placement, hplacement, cell, hcell, hedgePlacement,
    edge_mem_of_directedEdgeCoefficient_eq_one boundary
      (cellBoundaryEdgeAt cell .side₅) hboundaryCoefficient⟩

structure CurrentRightmostExposedEdge {m : ℕ}
    (placements : Finset (LiteralPlacement m))
    (boundary : List LabeledHexEdge) where
  placement : LiteralPlacement m
  placement_mem : placement ∈ placements
  cell : Cell
  cell_mem : cell ∈ placement.cells
  neighbor_outside : neighboringCell cell .side₅ ∉
    placementUnionCells placements
  placement_edge_mem :
    cellBoundaryEdgeAt cell .side₅ ∈
      literalPlacementBoundary placement
  boundary_edge_mem :
    cellBoundaryEdgeAt cell .side₅ ∈ boundary

theorem currentRightmostExposedEdge_nonempty {m : ℕ}
    (tiling : LiteralTiling m)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ tiling.1)
    (hplacements : placements.Nonempty)
    (boundary : List LabeledHexEdge)
    (hinvariant : RightmostBoundaryCoefficientInvariant boundary placements) :
    Nonempty (CurrentRightmostExposedEdge placements boundary) := by
  obtain ⟨placement, hplacement, cell, hcell,
      hneighbor, hedgePlacement⟩ :=
    exists_rightmost_exposed_placement hplacements
  have hplacementCoefficient :=
    exposed_edge_placementBoundaryList_coefficient_one
      tiling placements hsubset hplacement hcell hneighbor
  have hboundaryCoefficient :
      directedEdgeCoefficient boundary
        (cellBoundaryEdgeAt cell .side₅) = 1 := by
    rw [hinvariant cell]
    exact hplacementCoefficient
  have hedgeBoundary :=
    edge_mem_of_directedEdgeCoefficient_eq_one boundary
      (cellBoundaryEdgeAt cell .side₅) hboundaryCoefficient
  exact ⟨⟨placement, hplacement, cell, hcell,
    hneighbor, hedgePlacement, hedgeBoundary⟩⟩

end BenzelProblem6Kernel
