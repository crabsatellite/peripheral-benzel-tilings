import D4KernelOnly.GeneralClassZeroPeeling
import BenzelProblem6Kernel.TilingComplexEdgePairs

/-! # Duplicate-free reverse-closed class-zero tiling complex -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czCPerimeterEdge_has_cellSide
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ czCPerimeterEdges s r) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  rw [czCPerimeterEdges, List.mem_append] at hedge
  rcases hedge with hp | hn
  · obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hp
    exact ⟨cell, .side₅, rfl⟩
  · obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hn
    refine ⟨neighboringCell cell .side₅, .side₂, ?_⟩
    simpa [oppositeHexSide] using cellBoundaryEdgeAt_neighbor_exact cell .side₅

theorem czBPerimeterEdge_has_cellSide
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ czBPerimeterEdges s r) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hedge
  obtain ⟨cell, side, hcell⟩ := czCPerimeterEdge_has_cellSide hsource
  refine ⟨d4RotateCell cell, d4RotateSide side, ?_⟩
  rw [← d4RotateEdge_cellBoundaryEdgeAt, hcell]

theorem czAPerimeterEdge_has_cellSide
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ czAPerimeterEdges s r) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hedge
  obtain ⟨cell, side, hcell⟩ := czBPerimeterEdge_has_cellSide hsource
  refine ⟨d4RotateCell cell, d4RotateSide side, ?_⟩
  rw [← d4RotateEdge_cellBoundaryEdgeAt, hcell]

theorem czPerimeterEdge_has_cellSide
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ czPerimeterEdges s r) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  rw [czPerimeterEdges, List.mem_append, List.mem_append] at hedge
  rcases hedge with (hc | hb) | ha
  · exact czCPerimeterEdge_has_cellSide hc
  · exact czBPerimeterEdge_has_cellSide hb
  · exact czAPerimeterEdge_has_cellSide ha

theorem czReducedBoundaryEdge_has_cellSide
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r) {edge : LabeledHexEdge}
    (hedge : edge ∈ czReducedBoundaryWalk s r) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge :=
  czPerimeterEdge_has_cellSide
    ((czPerimeterEdges_perm_reduced s r hs hr).mem_iff.mpr hedge)

theorem czReducedBoundary_same_cell_chain
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    SameOrientedBoundaryChain (czReducedBoundaryWalk s r)
      (orientedCellBoundaryList
        (offsetCellValueList (2 * s + r - 2) (3 * s))) := by
  intro edge
  by_cases hside : ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge
  · obtain ⟨cell, side, rfl⟩ := hside
    exact directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr cell side
  · have hnotReduced : edge ∉ czReducedBoundaryWalk s r := by
      intro h; exact hside (czReducedBoundaryEdge_has_cellSide hs hr h)
    have hnotCell : edge ∉ orientedCellBoundaryList
        (offsetCellValueList (2 * s + r - 2) (3 * s)) := by
      intro h; exact hside (orientedOffsetCellBoundaryEdge_has_cellSide h)
    have hnotReverseReduced : reverseLabeledHexEdge edge ∉
        czReducedBoundaryWalk s r := by
      intro h
      apply hside
      exact cmoReverse_cellSide_has_cellSide
        (czReducedBoundaryEdge_has_cellSide hs hr h)
    have hnotReverseCell : reverseLabeledHexEdge edge ∉
        orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)) := by
      intro h
      apply hside
      exact cmoReverse_cellSide_has_cellSide
        (orientedOffsetCellBoundaryEdge_has_cellSide h)
    simp [directedEdgeCoefficient, List.count_eq_zero.mpr,
      hnotReduced, hnotCell, hnotReverseReduced, hnotReverseCell]

theorem czReducedBoundary_same_placement_chain
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    SameOrientedBoundaryChain (czReducedBoundaryWalk s r)
      (literalPlacementBoundaryList (offsetShadowPlacementFinset tiling).toList) :=
  (czReducedBoundary_same_cell_chain s r hs hr).trans
    (offsetShadowPlacementFinsetBoundaries_eq_cellBoundaries tiling).symm

theorem offsetShadowPlacementBoundaries_disjoint
    {t d : ℕ} (tiling : OffsetLiteralTiling t d)
    {left right : LiteralPlacement t}
    (hleft : left ∈ offsetShadowPlacementFinset tiling)
    (hright : right ∈ offsetShadowPlacementFinset tiling)
    (hne : left ≠ right) :
    List.Disjoint (literalPlacementBoundary left)
      (literalPlacementBoundary right) := by
  rw [List.disjoint_left]
  intro edge hedgeLeft hedgeRight
  obtain ⟨leftCell, hleftCell, hleftEdge⟩ :=
    literalPlacementBoundary_edge_has_cell left hedgeLeft
  obtain ⟨rightCell, hrightCell, hrightEdge⟩ :=
    literalPlacementBoundary_edge_has_cell right hedgeRight
  have hcell : leftCell = rightCell :=
    common_directed_cellBoundary_edge_forces_cell_eq hleftEdge hrightEdge
  subst rightCell
  exact hne (offsetShadowPlacement_unique_of_cell tiling hleft hright
    hleftCell hrightCell)

theorem offsetReverseShadowPlacementBoundaryList_nodup
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    (reverseLiteralPlacementBoundaryList
      (offsetShadowPlacementFinset tiling).toList).Nodup := by
  rw [reverseLiteralPlacementBoundaryList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact reverseLiteralPlacementBoundary_nodup placement
  · apply (Finset.nodup_toList
      (offsetShadowPlacementFinset tiling)).pairwise_of_forall_ne
    intro left hleft right hright hne
    apply reverseReorientedEdges_disjoint
    exact offsetShadowPlacementBoundaries_disjoint tiling
      (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne

theorem czReducedBoundary_inside_outside
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    {edge : LabeledHexEdge} (hedge : edge ∈ czReducedBoundaryWalk s r)
    {cell : Cell} {side : HexSide} (hcellSide : cellBoundaryEdgeAt cell side = edge) :
    inBenzel (2 * s + r) (s + 2 * r) cell ∧
      ¬inBenzel (2 * s + r) (s + 2 * r) (neighboringCell cell side) := by
  have hcoefficient : directedEdgeCoefficient (czReducedBoundaryWalk s r)
      (cellBoundaryEdgeAt cell side) = 1 := by
    rw [hcellSide]
    exact czPerimeterEdge_coefficient_one s r hs hr
      ((czPerimeterEdges_perm_reduced s r hs hr).mem_iff.mpr hedge)
  rw [directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr,
    offsetCellBoundaryCoefficient] at hcoefficient
  have hp := classZeroOffsetParameters s r hs hr
  rw [hp.1, hp.2] at hcoefficient
  by_cases hi : inBenzel (2 * s + r) (s + 2 * r) cell <;>
    by_cases hn : inBenzel (2 * s + r) (s + 2 * r)
      (neighboringCell cell side) <;> simp [hi, hn] at hcoefficient ⊢

theorem czReducedBoundary_disjoint_reverseTiling
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    List.Disjoint (czReducedBoundaryWalk s r)
      (reverseLiteralPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList) := by
  rw [List.disjoint_left]
  intro edge hedgeOuter hedgeTiles
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap] at hedgeTiles
  obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeTiles
  obtain ⟨cell, side, hcellSide⟩ := czReducedBoundaryEdge_has_cellSide hs hr hedgeOuter
  have hg := czReducedBoundary_inside_outside s r hs hr hedgeOuter hcellSide
  have horiginal : reverseLabeledHexEdge edge ∈ literalPlacementBoundary placement :=
    (mem_reverseReorientedEdges_iff edge _).mp hedgePlacement
  obtain ⟨owner, howner, hownerEdge⟩ :=
    literalPlacementBoundary_edge_has_cell placement horiginal
  have hownerEdge' : reverseLabeledHexEdge (cellBoundaryEdgeAt cell side) ∈
      labeledCellBoundary owner := by rwa [hcellSide]
  have hownerEq : owner = neighboringCell cell side :=
    (reverse_edge_mem_labeledCellBoundary_iff cell owner side).mp hownerEdge'
  obtain ⟨source, hsource, rfl⟩ :=
    (mem_offsetShadowPlacementFinset_iff tiling placement).1
      (Finset.mem_toList.mp hplacement)
  rw [offsetShadowPlacement_cells] at howner
  exact hg.2 (by
    rw [← hownerEq]
    have hm := source.2 owner howner
    have hp := classZeroOffsetParameters s r hs hr
    simpa [hp.1, hp.2] using hm)

noncomputable def czTilingComplexDirectedEdges
    {s r : ℕ} (_hs : 1 ≤ s) (_hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) : List LabeledHexEdge :=
  czReducedBoundaryWalk s r ++
    reverseLiteralPlacementBoundaryList (offsetShadowPlacementFinset tiling).toList

theorem czTilingComplexDirectedEdges_nodup
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czTilingComplexDirectedEdges hs hr tiling).Nodup := by
  rw [czTilingComplexDirectedEdges, List.nodup_append]
  exact ⟨czReducedBoundary_nodup s r,
    offsetReverseShadowPlacementBoundaryList_nodup tiling,
    czReducedBoundary_disjoint_reverseTiling hs hr tiling⟩

theorem czTilingComplexDirectedEdges_coefficient_zero
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) (edge : LabeledHexEdge) :
    directedEdgeCoefficient (czTilingComplexDirectedEdges hs hr tiling) edge = 0 := by
  rw [czTilingComplexDirectedEdges, directedEdgeCoefficient_append,
    cmoDirectedEdgeCoefficient_reversePlacementBoundaryList,
    czReducedBoundary_same_placement_chain hs hr tiling edge]
  ring

theorem czTilingComplexDirectedEdges_reverse_mem
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) {edge : LabeledHexEdge}
    (hedge : edge ∈ czTilingComplexDirectedEdges hs hr tiling) :
    reverseLabeledHexEdge edge ∈ czTilingComplexDirectedEdges hs hr tiling := by
  have hcount := lawful_count_eq_indicator_of_nodup
    (czTilingComplexDirectedEdges hs hr tiling)
    (czTilingComplexDirectedEdges_nodup hs hr tiling) edge
  have hcoeff := czTilingComplexDirectedEdges_coefficient_zero hs hr tiling edge
  rw [directedEdgeCoefficient, hcount] at hcoeff
  simp [hedge] at hcoeff
  by_contra hreverse
  rw [List.count_eq_zero.mpr hreverse] at hcoeff
  omega

end FiniteDefects
