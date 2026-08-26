import D4KernelOnly.D4ReducedPeelingBoundary

/-! # Every physical d=4 boundary edge is a literal cell-side edge -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def d4RotateSide : HexSide → HexSide
  | .side₀ => .side₄
  | .side₁ => .side₅
  | .side₂ => .side₀
  | .side₃ => .side₁
  | .side₄ => .side₂
  | .side₅ => .side₃

theorem d4RotateSide_three (side : HexSide) :
    d4RotateSide (d4RotateSide (d4RotateSide side)) = side := by
  cases side <;> rfl

theorem d4RotateEdge_cellBoundaryEdgeAt
    (cell : Cell) (side : HexSide) :
    d4RotateEdge (cellBoundaryEdgeAt cell side) =
      cellBoundaryEdgeAt (d4RotateCell cell) (d4RotateSide side) := by
  rcases cell with ⟨i, j⟩
  cases side
  all_goals
    apply labeledHexEdge_ext
  all_goals first
    | rfl
    | (apply Prod.ext <;>
        simp [d4RotateEdge, d4RotateVertex, d4RotateCell, d4RotateSide,
          cellBoundaryEdgeAt, hexCellStartVertex, hexCellCenter,
          advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
          ShadowStep.neg] <;> ring)

theorem d4RotateEdge_three (edge : LabeledHexEdge) :
    d4RotateEdge (d4RotateEdge (d4RotateEdge edge)) = edge := by
  rcases edge with ⟨source, target, label⟩
  apply labeledHexEdge_ext
  · rcases source with ⟨x, y⟩
    apply Prod.ext <;> simp [d4RotateEdge, d4RotateVertex] <;> ring
  · rcases target with ⟨x, y⟩
    apply Prod.ext <;> simp [d4RotateEdge, d4RotateVertex] <;> ring
  · cases label <;> rfl

theorem d4RotateBoundaryEdge_mem {m : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ d4LiteralBoundaryWalk m) :
    d4RotateEdge edge ∈ d4LiteralBoundaryWalk m := by
  have hsource : d4RotateEdge edge ∈
      (d4LiteralBoundaryWalk m).map d4RotateEdge :=
    List.mem_map.mpr ⟨edge, hedge, rfl⟩
  exact (d4LiteralBoundaryWalk_rotate_perm m).mem_iff.mp hsource

theorem d4RotateBoundaryEdge_twice_mem {m : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ d4LiteralBoundaryWalk m) :
    d4RotateEdge (d4RotateEdge edge) ∈ d4LiteralBoundaryWalk m :=
  d4RotateBoundaryEdge_mem (d4RotateBoundaryEdge_mem hedge)

theorem d4CBoundaryEdge_has_cellSide {m : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ d4LiteralBoundaryWalk m)
    (hlabel : edge.label = .c) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  rcases d4Cedge_forward_or_reverse hedge hlabel with hforward | hreverse
  · have hfilter : edge ∈
        forwardSideFiveEdges (d4LiteralBoundaryWalk m) := by
      exact List.mem_filter.mpr ⟨hedge, hforward⟩
    rw [d4LiteralBoundaryWalk_forward, d4WalkForwardSideFiveEdges] at hfilter
    obtain ⟨cell, hcell, hedgeEq⟩ := List.mem_map.mp hfilter
    exact ⟨cell, .side₅, hedgeEq⟩
  · have hfilter : edge ∈
        reverseSideFiveEdges (d4LiteralBoundaryWalk m) := by
      exact List.mem_filter.mpr ⟨hedge, hreverse⟩
    rw [d4LiteralBoundaryWalk_reverse, d4WalkReverseSideFiveEdges] at hfilter
    obtain ⟨cell, hcell, hedgeEq⟩ := List.mem_map.mp hfilter
    refine ⟨neighboringCell cell .side₅, .side₂, ?_⟩
    have hgeom := cellBoundaryEdgeAt_neighbor_exact cell .side₅
    simp only [oppositeHexSide] at hgeom
    rw [hgeom]
    exact hedgeEq

theorem d4LiteralBoundaryEdge_has_cellSide {m : ℕ}
    {edge : LabeledHexEdge} (hedge : edge ∈ d4LiteralBoundaryWalk m) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  cases hlabel : edge.label
  · have hrotMem := d4RotateBoundaryEdge_mem hedge
    have hrotLabel : (d4RotateEdge edge).label = .c := by
      simp [d4RotateEdge, d4RotateLabel, hlabel]
    obtain ⟨cell, side, hcell⟩ :=
      d4CBoundaryEdge_has_cellSide hrotMem hrotLabel
    refine ⟨d4RotateCell (d4RotateCell cell),
      d4RotateSide (d4RotateSide side), ?_⟩
    have htwice := congrArg (fun candidate =>
      d4RotateEdge (d4RotateEdge candidate)) hcell
    change d4RotateEdge (d4RotateEdge (cellBoundaryEdgeAt cell side)) =
      d4RotateEdge (d4RotateEdge (d4RotateEdge edge)) at htwice
    rw [d4RotateEdge_cellBoundaryEdgeAt,
      d4RotateEdge_cellBoundaryEdgeAt] at htwice
    simpa [d4RotateEdge_three] using htwice
  · have hrotMem := d4RotateBoundaryEdge_twice_mem hedge
    have hrotLabel :
        (d4RotateEdge (d4RotateEdge edge)).label = .c := by
      simp [d4RotateEdge, d4RotateLabel, hlabel]
    obtain ⟨cell, side, hcell⟩ :=
      d4CBoundaryEdge_has_cellSide hrotMem hrotLabel
    refine ⟨d4RotateCell cell, d4RotateSide side, ?_⟩
    have honce := congrArg d4RotateEdge hcell
    change d4RotateEdge (cellBoundaryEdgeAt cell side) =
      d4RotateEdge (d4RotateEdge (d4RotateEdge edge)) at honce
    rw [d4RotateEdge_cellBoundaryEdgeAt] at honce
    simpa [d4RotateEdge_three] using honce
  · exact d4CBoundaryEdge_has_cellSide hedge hlabel

theorem d4ReducedBoundaryEdge_has_cellSide {m : ℕ}
    {edge : LabeledHexEdge} (hedge : edge ∈ d4ReducedBoundaryWalk m) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge :=
  d4LiteralBoundaryEdge_has_cellSide
    ((reduceGeometricBacktracks_sublist _).subset hedge)

end FiniteDefects
