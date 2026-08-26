import D4KernelOnly.D4PerimeterEdges
import BenzelProblem6Kernel.TilingComplexEdgePairs

/-! # The duplicate-free, reverse-closed d=4 tiling complex -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem d4PerimeterEdges_perm_reduced (m : ℕ) :
    List.Perm (d4PerimeterEdges m) (d4ReducedBoundaryWalk m) := by
  have hsubset : (d4PerimeterEdges m).toFinset ⊆
      (d4ReducedBoundaryWalk m).toFinset := by
    intro edge hedge
    exact List.mem_toFinset.mpr
      (d4PerimeterEdges_subset_reduced m edge (List.mem_toFinset.mp hedge))
  have hcard : (d4ReducedBoundaryWalk m).toFinset.card ≤
      (d4PerimeterEdges m).toFinset.card := by
    rw [List.toFinset_card_of_nodup (d4ReducedBoundary_nodup m),
      List.toFinset_card_of_nodup (d4PerimeterEdges_nodup m),
      d4ReducedBoundary_length, d4PerimeterEdges_length]
  have hfinset := Finset.eq_of_subset_of_card_le hsubset hcard
  apply (List.perm_ext_iff_of_nodup
    (d4PerimeterEdges_nodup m) (d4ReducedBoundary_nodup m)).mpr
  intro edge
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp hfinset edge

theorem reverse_cellSide_has_cellSide
    {edge : LabeledHexEdge}
    (hreverse : ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = reverseLabeledHexEdge edge) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  obtain ⟨cell, side, hcell⟩ := hreverse
  refine ⟨neighboringCell cell side, oppositeHexSide side, ?_⟩
  rw [cellBoundaryEdgeAt_neighbor_exact, hcell,
    reverseLabeledHexEdge_involutive]

theorem orientedD4CellBoundaryEdge_has_cellSide {m : ℕ}
    {edge : LabeledHexEdge}
    (hedge : edge ∈ orientedCellBoundaryList (d4CellValueList m)) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  simp only [orientedCellBoundaryList, List.mem_flatMap] at hedge
  obtain ⟨cell, hcell, hedgeCell⟩ := hedge
  obtain ⟨side, hside⟩ := labeledCellBoundary_edge_has_side hedgeCell
  exact ⟨cell, side, hside⟩

theorem d4ReducedBoundary_same_cell_chain (m : ℕ) :
    SameOrientedBoundaryChain (d4ReducedBoundaryWalk m)
      (orientedCellBoundaryList (d4CellValueList m)) := by
  intro edge
  by_cases hside : ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge
  · obtain ⟨cell, side, rfl⟩ := hside
    exact directedEdgeCoefficient_d4ReducedBoundary_allSides m cell side
  · have hnotReduced : edge ∉ d4ReducedBoundaryWalk m := by
      intro hmem
      exact hside (d4ReducedBoundaryEdge_has_cellSide hmem)
    have hnotCell : edge ∉ orientedCellBoundaryList (d4CellValueList m) := by
      intro hmem
      exact hside (orientedD4CellBoundaryEdge_has_cellSide hmem)
    have hnotReverseReduced : reverseLabeledHexEdge edge ∉
        d4ReducedBoundaryWalk m := by
      intro hmem
      apply hside
      exact reverse_cellSide_has_cellSide
        (d4ReducedBoundaryEdge_has_cellSide hmem)
    have hnotReverseCell : reverseLabeledHexEdge edge ∉
        orientedCellBoundaryList (d4CellValueList m) := by
      intro hmem
      apply hside
      exact reverse_cellSide_has_cellSide
        (orientedD4CellBoundaryEdge_has_cellSide hmem)
    simp [directedEdgeCoefficient, List.count_eq_zero.mpr,
      hnotReduced, hnotCell, hnotReverseReduced, hnotReverseCell]

theorem d4ReducedBoundary_same_placement_chain {m : ℕ}
    (tiling : D4LiteralTiling m) :
    SameOrientedBoundaryChain (d4ReducedBoundaryWalk m)
      (literalPlacementBoundaryList
        (d4ShadowPlacementFinset tiling).toList) :=
  (d4ReducedBoundary_same_cell_chain m).trans
    (d4ShadowPlacementFinsetBoundaries_eq_d4CellBoundaries tiling).symm

theorem d4ShadowPlacementBoundaries_disjoint {m : ℕ}
    (tiling : D4LiteralTiling m)
    {left right : LiteralPlacement m}
    (hleft : left ∈ d4ShadowPlacementFinset tiling)
    (hright : right ∈ d4ShadowPlacementFinset tiling)
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
  exact hne (d4ShadowPlacement_unique_of_cell tiling hleft hright
    hleftCell hrightCell)

theorem d4ShadowPlacementBoundaryList_nodup {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (literalPlacementBoundaryList
      (d4ShadowPlacementFinset tiling).toList).Nodup := by
  rw [literalPlacementBoundaryList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact literalPlacementBoundary_nodup placement
  · apply (Finset.nodup_toList
      (d4ShadowPlacementFinset tiling)).pairwise_of_forall_ne
    intro left hleft right hright hne
    exact d4ShadowPlacementBoundaries_disjoint tiling
      (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne

theorem d4ReverseShadowPlacementBoundaryList_nodup {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (reverseLiteralPlacementBoundaryList
      (d4ShadowPlacementFinset tiling).toList).Nodup := by
  rw [reverseLiteralPlacementBoundaryList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact reverseLiteralPlacementBoundary_nodup placement
  · apply (Finset.nodup_toList
      (d4ShadowPlacementFinset tiling)).pairwise_of_forall_ne
    intro left hleft right hright hne
    apply reverseReorientedEdges_disjoint
    exact d4ShadowPlacementBoundaries_disjoint tiling
      (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne

theorem d4ReducedBoundary_inside_outside {m : ℕ}
    {edge : LabeledHexEdge} (hedge : edge ∈ d4ReducedBoundaryWalk m)
    {cell : Cell} {side : HexSide} (hcellSide :
      cellBoundaryEdgeAt cell side = edge) :
    inBenzel (m + 4) (2 * m + 4) cell ∧
      ¬inBenzel (m + 4) (2 * m + 4) (neighboringCell cell side) := by
  have hcoefficient : directedEdgeCoefficient (d4ReducedBoundaryWalk m)
      (cellBoundaryEdgeAt cell side) = 1 := by
    rw [hcellSide]
    exact d4PerimeterEdge_coefficient_one m
      ((d4PerimeterEdges_perm_reduced m).mem_iff.mpr hedge)
  rw [directedEdgeCoefficient_d4ReducedBoundary_allSides,
    directedEdgeCoefficient_d4CellBoundaries] at hcoefficient
  by_cases hinside : inBenzel (m + 4) (2 * m + 4) cell <;>
    by_cases hneighbor : inBenzel (m + 4) (2 * m + 4)
      (neighboringCell cell side) <;> simp [hinside, hneighbor] at hcoefficient ⊢

theorem d4ReducedBoundary_disjoint_reversePlacement {m : ℕ}
    (tiling : D4LiteralTiling m)
    {placement : LiteralPlacement m}
    (hplacement : placement ∈ d4ShadowPlacementFinset tiling) :
    List.Disjoint (d4ReducedBoundaryWalk m)
      (reverseReorientedEdges (literalPlacementBoundary placement)) := by
  rw [List.disjoint_left]
  intro edge hedgeOuter hedgeTile
  obtain ⟨cell, side, hcellSide⟩ :=
    d4ReducedBoundaryEdge_has_cellSide hedgeOuter
  have hgeometry := d4ReducedBoundary_inside_outside hedgeOuter hcellSide
  have hreverseTile : reverseLabeledHexEdge edge ∈
      literalPlacementBoundary placement :=
    (mem_reverseReorientedEdges_iff edge _).mp hedgeTile
  obtain ⟨owner, howner, hownerEdge⟩ :=
    literalPlacementBoundary_edge_has_cell placement hreverseTile
  have hownerEdge' : reverseLabeledHexEdge
      (cellBoundaryEdgeAt cell side) ∈ labeledCellBoundary owner := by
    rwa [hcellSide]
  have hownerEq : owner = neighboringCell cell side :=
    (reverse_edge_mem_labeledCellBoundary_iff cell owner side).mp hownerEdge'
  obtain ⟨source, hsource, hsourceEq⟩ :=
    (mem_d4ShadowPlacementFinset_iff tiling placement).1 hplacement
  subst placement
  rw [d4ShadowPlacement_cells] at howner
  exact hgeometry.2 (by
    rw [← hownerEq]
    exact source.2 owner howner)

theorem d4ReducedBoundary_disjoint_reverseTiling {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List.Disjoint (d4ReducedBoundaryWalk m)
      (reverseLiteralPlacementBoundaryList
        (d4ShadowPlacementFinset tiling).toList) := by
  rw [List.disjoint_left]
  intro edge hedgeOuter hedgeTiles
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap] at hedgeTiles
  obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeTiles
  exact (List.disjoint_left.mp
    (d4ReducedBoundary_disjoint_reversePlacement tiling
      (Finset.mem_toList.mp hplacement))) hedgeOuter hedgePlacement

noncomputable def d4TilingComplexDirectedEdges {m : ℕ}
    (tiling : D4LiteralTiling m) : List LabeledHexEdge :=
  d4ReducedBoundaryWalk m ++ reverseLiteralPlacementBoundaryList
    (d4ShadowPlacementFinset tiling).toList

theorem d4TilingComplexDirectedEdges_nodup {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TilingComplexDirectedEdges tiling).Nodup := by
  rw [d4TilingComplexDirectedEdges, List.nodup_append]
  exact ⟨d4ReducedBoundary_nodup m,
    d4ReverseShadowPlacementBoundaryList_nodup tiling,
    d4ReducedBoundary_disjoint_reverseTiling tiling⟩

theorem directedEdgeCoefficient_reversePlacementBoundaryList {m : ℕ}
    (placements : List (LiteralPlacement m)) (edge : LabeledHexEdge) :
    directedEdgeCoefficient
        (reverseLiteralPlacementBoundaryList placements) edge =
      -directedEdgeCoefficient
        (literalPlacementBoundaryList placements) edge := by
  induction placements with
  | nil => simp [reverseLiteralPlacementBoundaryList,
      literalPlacementBoundaryList, directedEdgeCoefficient]
  | cons placement rest ih =>
      change directedEdgeCoefficient
          (reverseReorientedEdges (literalPlacementBoundary placement) ++
            reverseLiteralPlacementBoundaryList rest) edge =
        -directedEdgeCoefficient
          (literalPlacementBoundary placement ++
            literalPlacementBoundaryList rest) edge
      unfold reverseReorientedEdges
      rw [
        directedEdgeCoefficient_append, directedEdgeCoefficient_append,
        directedEdgeCoefficient_reverse, ih]
      ring

theorem d4TilingComplexDirectedEdges_coefficient_zero {m : ℕ}
    (tiling : D4LiteralTiling m) (edge : LabeledHexEdge) :
    directedEdgeCoefficient (d4TilingComplexDirectedEdges tiling) edge = 0 := by
  rw [d4TilingComplexDirectedEdges, directedEdgeCoefficient_append,
    directedEdgeCoefficient_reversePlacementBoundaryList,
    d4ReducedBoundary_same_placement_chain tiling edge]
  ring

theorem d4TilingComplexDirectedEdges_reverse_mem {m : ℕ}
    (tiling : D4LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ d4TilingComplexDirectedEdges tiling) :
    reverseLabeledHexEdge edge ∈ d4TilingComplexDirectedEdges tiling := by
  have hcount := lawful_count_eq_indicator_of_nodup
    (d4TilingComplexDirectedEdges tiling)
    (d4TilingComplexDirectedEdges_nodup tiling) edge
  have hcoefficient := d4TilingComplexDirectedEdges_coefficient_zero tiling edge
  rw [directedEdgeCoefficient, hcount] at hcoefficient
  simp [hedge] at hcoefficient
  by_contra hreverse
  rw [List.count_eq_zero.mpr hreverse] at hcoefficient
  omega

end FiniteDefects
