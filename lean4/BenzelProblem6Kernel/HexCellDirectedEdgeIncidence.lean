import BenzelProblem6Kernel.OrientedTilingCellBoundary

/-! # Exact directed incidence of a honeycomb cell side -/

namespace BenzelProblem6Kernel

theorem cellBoundaryEdgeAt_neighbor_exact
    (cell : Cell) (side : HexSide) :
    cellBoundaryEdgeAt (neighboringCell cell side)
        (oppositeHexSide side) =
      reverseLabeledHexEdge (cellBoundaryEdgeAt cell side) := by
  rcases cell with ⟨i, j⟩
  cases side <;>
    apply labeledHexEdge_ext <;>
    simp [cellBoundaryEdgeAt, neighboringCell, oppositeHexSide,
      reverseLabeledHexEdge, advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC] <;> omega

theorem cellBoundaryEdgeAt_nonloop
    (cell : Cell) (side : HexSide) :
    (cellBoundaryEdgeAt cell side).source ≠
      (cellBoundaryEdgeAt cell side).target := by
  rcases cell with ⟨i, j⟩
  cases side <;>
    simp [cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC]

theorem cellBoundaryEdgeAt_ne_reverse
    (cell : Cell) (side : HexSide) :
    cellBoundaryEdgeAt cell side ≠
      reverseLabeledHexEdge (cellBoundaryEdgeAt cell side) := by
  intro h
  have hsource := congrArg LabeledHexEdge.source h
  exact cellBoundaryEdgeAt_nonloop cell side hsource

theorem cellBoundaryEdgeAt_eq_iff
    (leftCell rightCell : Cell) (leftSide rightSide : HexSide) :
    cellBoundaryEdgeAt rightCell rightSide =
        cellBoundaryEdgeAt leftCell leftSide ↔
      rightCell = leftCell ∧ rightSide = leftSide := by
  constructor
  · intro hedge
    have hkey := congrArg LabeledHexEdge.key hedge
    rcases (cellBoundaryEdgeAt_key_eq_iff
      leftCell rightCell leftSide rightSide).mp hkey.symm with hsame | hneighbor
    · exact hsame
    · rcases hneighbor with ⟨rfl, rfl⟩
      rw [cellBoundaryEdgeAt_neighbor_exact] at hedge
      exact (cellBoundaryEdgeAt_ne_reverse leftCell leftSide hedge.symm).elim
  · rintro ⟨rfl, rfl⟩
    rfl

theorem edge_mem_labeledCellBoundary_iff
    (cell other : Cell) (side : HexSide) :
    cellBoundaryEdgeAt cell side ∈ labeledCellBoundary other ↔
      other = cell := by
  rw [labeledCellBoundary_eq_allEdges]
  constructor
  · intro hmem
    simp [allCellBoundaryEdges] at hmem
    rcases hmem with hedge | hedge | hedge | hedge | hedge | hedge
    · exact (cellBoundaryEdgeAt_eq_iff cell other side .side₀).mp hedge.symm |>.1
    · exact (cellBoundaryEdgeAt_eq_iff cell other side .side₁).mp hedge.symm |>.1
    · exact (cellBoundaryEdgeAt_eq_iff cell other side .side₂).mp hedge.symm |>.1
    · exact (cellBoundaryEdgeAt_eq_iff cell other side .side₃).mp hedge.symm |>.1
    · exact (cellBoundaryEdgeAt_eq_iff cell other side .side₄).mp hedge.symm |>.1
    · exact (cellBoundaryEdgeAt_eq_iff cell other side .side₅).mp hedge.symm |>.1
  · rintro rfl
    cases side <;> simp [allCellBoundaryEdges]

theorem reverse_edge_mem_labeledCellBoundary_iff
    (cell other : Cell) (side : HexSide) :
    reverseLabeledHexEdge (cellBoundaryEdgeAt cell side) ∈
        labeledCellBoundary other ↔
      other = neighboringCell cell side := by
  rw [← cellBoundaryEdgeAt_neighbor_exact]
  exact edge_mem_labeledCellBoundary_iff
    (neighboringCell cell side) other (oppositeHexSide side)

theorem labeledCellBoundary_nodup (cell : Cell) :
    (labeledCellBoundary cell).Nodup := by
  rcases cell with ⟨i, j⟩
  simp [labeledCellBoundary, walkLabeledHexEdges,
    cellBoundarySteps, advanceLabeledHexEdge, addHexStep,
    hexCellStartVertex, hexCellCenter, ShadowStep.neg,
    shadowA, shadowB, shadowC]

theorem count_cellBoundaryEdgeAt_labeledCellBoundary
    (cell other : Cell) (side : HexSide) :
    (labeledCellBoundary other).count (cellBoundaryEdgeAt cell side) =
      if other = cell then 1 else 0 := by
  simp [List.count_eq_of_nodup (labeledCellBoundary_nodup other),
    edge_mem_labeledCellBoundary_iff]

theorem count_reverseCellBoundaryEdgeAt_labeledCellBoundary
    (cell other : Cell) (side : HexSide) :
    (labeledCellBoundary other).count
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell side)) =
      if other = neighboringCell cell side then 1 else 0 := by
  simp [List.count_eq_of_nodup (labeledCellBoundary_nodup other),
    reverse_edge_mem_labeledCellBoundary_iff]

theorem count_cellBoundaryEdgeAt_orientedCellBoundaryList
    (cells : List Cell) (cell : Cell) (side : HexSide) :
    (orientedCellBoundaryList cells).count
        (cellBoundaryEdgeAt cell side) = cells.count cell := by
  induction cells with
  | nil => rfl
  | cons head rest ih =>
      change (rest.flatMap labeledCellBoundary).count
        (cellBoundaryEdgeAt cell side) = rest.count cell at ih
      rw [orientedCellBoundaryList, List.flatMap_cons,
        List.count_append,
        count_cellBoundaryEdgeAt_labeledCellBoundary,
        List.count_cons, ih]
      by_cases h : head = cell <;> simp [h, Nat.add_comm]

theorem count_reverseCellBoundaryEdgeAt_orientedCellBoundaryList
    (cells : List Cell) (cell : Cell) (side : HexSide) :
    (orientedCellBoundaryList cells).count
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell side)) =
      cells.count (neighboringCell cell side) := by
  induction cells with
  | nil => rfl
  | cons head rest ih =>
      change (rest.flatMap labeledCellBoundary).count
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell side)) =
          rest.count (neighboringCell cell side) at ih
      rw [orientedCellBoundaryList, List.flatMap_cons,
        List.count_append,
        count_reverseCellBoundaryEdgeAt_labeledCellBoundary,
        List.count_cons, ih]
      by_cases h : head = neighboringCell cell side <;>
        simp [h, Nat.add_comm]

theorem directedEdgeCoefficient_orientedCellBoundaryList
    (cells : List Cell) (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient (orientedCellBoundaryList cells)
        (cellBoundaryEdgeAt cell side) =
      (cells.count cell : ℤ) -
        cells.count (neighboringCell cell side) := by
  rw [directedEdgeCoefficient,
    count_cellBoundaryEdgeAt_orientedCellBoundaryList,
    count_reverseCellBoundaryEdgeAt_orientedCellBoundaryList]

end BenzelProblem6Kernel
