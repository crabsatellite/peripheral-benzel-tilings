import D4KernelOnly.GeneralClassMinusOnePerimeter
import BenzelProblem6Kernel.TilingComplexEdgePairs

/-! # Duplicate-free reverse-closed class-minus-one tiling complex -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 1000000

theorem cmoRotateBoundaryEdge_mem
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ classMinusOneLiteralBoundaryWalk s r) :
    d4RotateEdge edge ∈ classMinusOneLiteralBoundaryWalk s r := by
  have hsource : d4RotateEdge edge ∈
      (classMinusOneLiteralBoundaryWalk s r).map d4RotateEdge :=
    List.mem_map.mpr ⟨edge, hedge, rfl⟩
  exact (classMinusOneBoundaryWalk_rotate_perm s r).mem_iff.mp hsource

theorem cmoRotateBoundaryEdge_twice_mem
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ classMinusOneLiteralBoundaryWalk s r) :
    d4RotateEdge (d4RotateEdge edge) ∈
      classMinusOneLiteralBoundaryWalk s r :=
  cmoRotateBoundaryEdge_mem (cmoRotateBoundaryEdge_mem hedge)

theorem cmoCBoundaryEdge_has_cellSide
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ classMinusOneLiteralBoundaryWalk s r)
    (hlabel : edge.label = .c) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  rcases cmoCedge_forward_or_reverse hedge hlabel with hforward | hreverse
  · have hfilter : edge ∈ forwardSideFiveEdges
        (classMinusOneLiteralBoundaryWalk s r) :=
      List.mem_filter.mpr ⟨hedge, hforward⟩
    rw [classMinusOneBoundaryWalk_forward,
      cmoWalkForwardSideFiveEdges] at hfilter
    obtain ⟨cell, hcell, hedgeEq⟩ := List.mem_map.mp hfilter
    exact ⟨cell, .side₅, hedgeEq⟩
  · have hfilter : edge ∈ reverseSideFiveEdges
        (classMinusOneLiteralBoundaryWalk s r) :=
      List.mem_filter.mpr ⟨hedge, hreverse⟩
    rw [classMinusOneBoundaryWalk_reverse,
      cmoWalkReverseSideFiveEdges] at hfilter
    obtain ⟨cell, hcell, hedgeEq⟩ := List.mem_map.mp hfilter
    refine ⟨neighboringCell cell .side₅, .side₂, ?_⟩
    have hgeom := cellBoundaryEdgeAt_neighbor_exact cell .side₅
    simp only [oppositeHexSide] at hgeom
    rw [hgeom]
    exact hedgeEq

theorem cmoLiteralBoundaryEdge_has_cellSide
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ classMinusOneLiteralBoundaryWalk s r) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  cases hlabel : edge.label
  · have hrotMem := cmoRotateBoundaryEdge_mem hedge
    have hrotLabel : (d4RotateEdge edge).label = .c := by
      simp [d4RotateEdge, d4RotateLabel, hlabel]
    obtain ⟨cell, side, hcell⟩ :=
      cmoCBoundaryEdge_has_cellSide hrotMem hrotLabel
    refine ⟨d4RotateCell (d4RotateCell cell),
      d4RotateSide (d4RotateSide side), ?_⟩
    have htwice := congrArg (fun candidate =>
      d4RotateEdge (d4RotateEdge candidate)) hcell
    change d4RotateEdge (d4RotateEdge (cellBoundaryEdgeAt cell side)) =
      d4RotateEdge (d4RotateEdge (d4RotateEdge edge)) at htwice
    rw [d4RotateEdge_cellBoundaryEdgeAt,
      d4RotateEdge_cellBoundaryEdgeAt] at htwice
    simpa [d4RotateEdge_three] using htwice
  · have hrotMem := cmoRotateBoundaryEdge_twice_mem hedge
    have hrotLabel :
        (d4RotateEdge (d4RotateEdge edge)).label = .c := by
      simp [d4RotateEdge, d4RotateLabel, hlabel]
    obtain ⟨cell, side, hcell⟩ :=
      cmoCBoundaryEdge_has_cellSide hrotMem hrotLabel
    refine ⟨d4RotateCell cell, d4RotateSide side, ?_⟩
    have honce := congrArg d4RotateEdge hcell
    change d4RotateEdge (cellBoundaryEdgeAt cell side) =
      d4RotateEdge (d4RotateEdge (d4RotateEdge edge)) at honce
    rw [d4RotateEdge_cellBoundaryEdgeAt] at honce
    simpa [d4RotateEdge_three] using honce
  · exact cmoCBoundaryEdge_has_cellSide hedge hlabel

theorem cmoReducedBoundaryEdge_has_cellSide
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ cmoReducedBoundaryWalk s r) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge :=
  cmoLiteralBoundaryEdge_has_cellSide
    ((reduceGeometricBacktracks_sublist _).subset hedge)

theorem orientedOffsetCellBoundaryEdge_has_cellSide
    {t d : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ orientedCellBoundaryList (offsetCellValueList t d)) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  simp only [orientedCellBoundaryList, List.mem_flatMap] at hedge
  obtain ⟨cell, hcell, hedgeCell⟩ := hedge
  obtain ⟨side, hside⟩ := labeledCellBoundary_edge_has_side hedgeCell
  exact ⟨cell, side, hside⟩

theorem cmoReverse_cellSide_has_cellSide
    {edge : LabeledHexEdge}
    (hreverse : ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = reverseLabeledHexEdge edge) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  obtain ⟨cell, side, hcell⟩ := hreverse
  refine ⟨neighboringCell cell side, oppositeHexSide side, ?_⟩
  rw [cellBoundaryEdgeAt_neighbor_exact, hcell,
    reverseLabeledHexEdge_involutive]

theorem cmoReducedBoundary_same_cell_chain
    (s r : ℕ) (hs : 1 ≤ s) :
    SameOrientedBoundaryChain (cmoReducedBoundaryWalk s r)
      (orientedCellBoundaryList
        (offsetCellValueList (2 * s + r - 1) (3 * s + 1))) := by
  intro edge
  by_cases hside : ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge
  · obtain ⟨cell, side, rfl⟩ := hside
    exact directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs cell side
  · have hnotReduced : edge ∉ cmoReducedBoundaryWalk s r := by
      intro hmem
      exact hside (cmoReducedBoundaryEdge_has_cellSide hmem)
    have hnotCell : edge ∉ orientedCellBoundaryList
        (offsetCellValueList (2 * s + r - 1) (3 * s + 1)) := by
      intro hmem
      exact hside (orientedOffsetCellBoundaryEdge_has_cellSide hmem)
    have hnotReverseReduced : reverseLabeledHexEdge edge ∉
        cmoReducedBoundaryWalk s r := by
      intro hmem
      apply hside
      exact cmoReverse_cellSide_has_cellSide
        (cmoReducedBoundaryEdge_has_cellSide hmem)
    have hnotReverseCell : reverseLabeledHexEdge edge ∉
        orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)) := by
      intro hmem
      apply hside
      exact cmoReverse_cellSide_has_cellSide
        (orientedOffsetCellBoundaryEdge_has_cellSide hmem)
    simp [directedEdgeCoefficient, List.count_eq_zero.mpr,
      hnotReduced, hnotCell, hnotReverseReduced, hnotReverseCell]

theorem cmoReducedBoundary_same_placement_chain
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    SameOrientedBoundaryChain (cmoReducedBoundaryWalk s r)
      (literalPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList) :=
  (cmoReducedBoundary_same_cell_chain s r hs).trans
    (cmoShadowPlacementFinsetBoundaries_eq_cellBoundaries tiling).symm

theorem cmoShadowPlacementBoundaries_disjoint
    {s r : ℕ} (tiling : CMOLiteralTiling s r)
    {left right : LiteralPlacement (2 * s + r - 1)}
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
  exact hne (cmoShadowPlacement_unique_of_cell tiling hleft hright
    hleftCell hrightCell)

theorem cmoShadowPlacementBoundaryList_nodup
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    (literalPlacementBoundaryList
      (offsetShadowPlacementFinset tiling).toList).Nodup := by
  rw [literalPlacementBoundaryList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact literalPlacementBoundary_nodup placement
  · apply (Finset.nodup_toList
      (offsetShadowPlacementFinset tiling)).pairwise_of_forall_ne
    intro left hleft right hright hne
    exact cmoShadowPlacementBoundaries_disjoint tiling
      (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne

theorem cmoReverseShadowPlacementBoundaryList_nodup
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
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
    exact cmoShadowPlacementBoundaries_disjoint tiling
      (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne

theorem cmoReducedBoundary_inside_outside
    (s r : ℕ) (hs : 1 ≤ s)
    {edge : LabeledHexEdge} (hedge : edge ∈ cmoReducedBoundaryWalk s r)
    {cell : Cell} {side : HexSide}
    (hcellSide : cellBoundaryEdgeAt cell side = edge) :
    inBenzel (2 * s + r + 1) (s + 2 * r + 1) cell ∧
      ¬inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (neighboringCell cell side) := by
  have hcoefficient : directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
      (cellBoundaryEdgeAt cell side) = 1 := by
    rw [hcellSide]
    exact cmoPerimeterEdge_coefficient_one s r hs
      ((cmoPerimeterEdges_perm_reduced s r hs).mem_iff.mpr hedge)
  rw [directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs,
    offsetCellBoundaryCoefficient] at hcoefficient
  have hp := classMinusOneOffsetParameters s r hs
  rw [hp.1, hp.2] at hcoefficient
  by_cases hinside : inBenzel (2 * s + r + 1) (s + 2 * r + 1) cell <;>
    by_cases hneighbor : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
      (neighboringCell cell side) <;>
    simp [hinside, hneighbor] at hcoefficient ⊢

theorem cmoReducedBoundary_disjoint_reversePlacement
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {placement : LiteralPlacement (2 * s + r - 1)}
    (hplacement : placement ∈ offsetShadowPlacementFinset tiling) :
    List.Disjoint (cmoReducedBoundaryWalk s r)
      (reverseReorientedEdges (literalPlacementBoundary placement)) := by
  rw [List.disjoint_left]
  intro edge hedgeOuter hedgeTile
  obtain ⟨cell, side, hcellSide⟩ :=
    cmoReducedBoundaryEdge_has_cellSide hedgeOuter
  have hgeometry := cmoReducedBoundary_inside_outside s r hs hedgeOuter hcellSide
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
    (mem_offsetShadowPlacementFinset_iff tiling placement).1 hplacement
  subst placement
  rw [offsetShadowPlacement_cells] at howner
  exact hgeometry.2 (by
    rw [← hownerEq]
    have hmem := source.2 owner howner
    have hp := classMinusOneOffsetParameters s r hs
    simpa [hp.1, hp.2] using hmem)

theorem cmoReducedBoundary_disjoint_reverseTiling
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    List.Disjoint (cmoReducedBoundaryWalk s r)
      (reverseLiteralPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList) := by
  rw [List.disjoint_left]
  intro edge hedgeOuter hedgeTiles
  rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap] at hedgeTiles
  obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeTiles
  exact (List.disjoint_left.mp
    (cmoReducedBoundary_disjoint_reversePlacement hs tiling
      (Finset.mem_toList.mp hplacement))) hedgeOuter hedgePlacement

noncomputable def cmoTilingComplexDirectedEdges
    {s r : ℕ} (_hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    List LabeledHexEdge :=
  cmoReducedBoundaryWalk s r ++ reverseLiteralPlacementBoundaryList
    (offsetShadowPlacementFinset tiling).toList

theorem cmoDirectedEdgeCoefficient_reversePlacementBoundaryList
    {m : ℕ} (placements : List (LiteralPlacement m))
    (edge : LabeledHexEdge) :
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
      rw [directedEdgeCoefficient_append, directedEdgeCoefficient_append,
        directedEdgeCoefficient_reverse, ih]
      ring

theorem cmoTilingComplexDirectedEdges_nodup
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoTilingComplexDirectedEdges hs tiling).Nodup := by
  rw [cmoTilingComplexDirectedEdges, List.nodup_append]
  exact ⟨cmoReducedBoundary_nodup s r hs,
    cmoReverseShadowPlacementBoundaryList_nodup tiling,
    cmoReducedBoundary_disjoint_reverseTiling hs tiling⟩

theorem cmoTilingComplexDirectedEdges_coefficient_zero
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    (edge : LabeledHexEdge) :
    directedEdgeCoefficient (cmoTilingComplexDirectedEdges hs tiling) edge = 0 := by
  rw [cmoTilingComplexDirectedEdges, directedEdgeCoefficient_append,
    cmoDirectedEdgeCoefficient_reversePlacementBoundaryList,
    cmoReducedBoundary_same_placement_chain hs tiling edge]
  ring

theorem cmoTilingComplexDirectedEdges_reverse_mem
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ cmoTilingComplexDirectedEdges hs tiling) :
    reverseLabeledHexEdge edge ∈ cmoTilingComplexDirectedEdges hs tiling := by
  have hcount := lawful_count_eq_indicator_of_nodup
    (cmoTilingComplexDirectedEdges hs tiling)
    (cmoTilingComplexDirectedEdges_nodup hs tiling) edge
  have hcoefficient := cmoTilingComplexDirectedEdges_coefficient_zero
    hs tiling edge
  rw [directedEdgeCoefficient, hcount] at hcoefficient
  simp [hedge] at hcoefficient
  by_contra hreverse
  rw [List.count_eq_zero.mpr hreverse] at hcoefficient
  omega

end FiniteDefects
