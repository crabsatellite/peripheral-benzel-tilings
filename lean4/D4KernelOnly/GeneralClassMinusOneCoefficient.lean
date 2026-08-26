import D4KernelOnly.GeneralClassMinusOneBoundaryCells
import D4KernelOnly.D4BoundarySideFiveCoefficient

/-! # Exact side-five coefficient identity for class-minus-one benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem mem_cmoWalkForwardSideFiveCells_iff
    (s r : ℕ) (cell : Cell) :
    cell ∈ cmoWalkForwardSideFiveCells s r ↔
      cell = cmoSpurCell s r ∨ cell ∈ cmoSideFiveCells s r := by
  rw [cmoWalkForwardSideFiveCells_eq]
  simp

theorem cmoLiteralBoundaryWalk_forward_count
    (s r : ℕ) (cell : Cell) :
    (classMinusOneLiteralBoundaryWalk s r).count
        (cellBoundaryEdgeAt cell .side₅) =
      (cmoWalkForwardSideFiveCells s r).count cell := by
  have hfilter := count_filter_eq_count_of_true
    (classMinusOneLiteralBoundaryWalk s r) isForwardSideFiveEdge
      (cellBoundaryEdgeAt cell .side₅)
      (isForwardSideFiveEdge_cellBoundaryEdgeAt cell)
  rw [← forwardSideFiveEdges] at hfilter
  rw [classMinusOneBoundaryWalk_forward,
    cmoWalkForwardSideFiveEdges,
    lawful_count_map_of_injective _ _
      cellBoundaryEdgeAt_sideFive_injective] at hfilter
  exact hfilter.symm

theorem cmoLiteralBoundaryWalk_reverse_count
    (s r : ℕ) (cell : Cell) :
    (classMinusOneLiteralBoundaryWalk s r).count
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) =
      (cmoWalkReverseSideFiveCells s r).count cell := by
  have hfilter := count_filter_eq_count_of_true
    (classMinusOneLiteralBoundaryWalk s r) isReverseSideFiveEdge
      (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅))
      (isReverseSideFiveEdge_reverse_cellBoundaryEdgeAt cell)
  rw [← reverseSideFiveEdges] at hfilter
  rw [classMinusOneBoundaryWalk_reverse,
    cmoWalkReverseSideFiveEdges,
    lawful_count_map_of_injective _ _
      reverse_cellBoundaryEdgeAt_sideFive_injective] at hfilter
  exact hfilter.symm

theorem cmoWalkSideFiveCell_count_difference
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    ((cmoWalkForwardSideFiveCells s r).count cell : ℤ) -
        (cmoWalkReverseSideFiveCells s r).count cell =
      (if cell ∈ cmoSideFiveCells s r then (1 : ℤ) else 0) -
        (if cell ∈ cmoSideFiveNegativeCells s r then (1 : ℤ) else 0) := by
  rw [lawful_count_eq_indicator_of_nodup _
      (cmoWalkForwardSideFiveCells_nodup s r hs),
    lawful_count_eq_indicator_of_nodup _
      (cmoWalkReverseSideFiveCells_nodup s r)]
  simp only [mem_cmoWalkForwardSideFiveCells_iff,
    mem_cmoWalkReverseSideFiveCells_iff s r hs]
  by_cases hspur : cell = cmoSpurCell s r
  · subst cell
    simp [cmoSpur_not_positive s r hs, cmoSpur_not_negative s r hs]
  · simp [hspur]

theorem offsetCellBoundaryCoefficient_sideFive
    (t d : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList (offsetCellValueList t d))
        (cellBoundaryEdgeAt cell .side₅) =
      (if inBenzel (t + 2) (offsetB t d) cell then (1 : ℤ) else 0) -
        (if inBenzel (t + 2) (offsetB t d)
          (neighboringCell cell .side₅) then (1 : ℤ) else 0) := by
  rw [directedEdgeCoefficient_orientedCellBoundaryList]
  have hcellCount := lawful_count_eq_indicator_of_nodup
    (offsetCellValueList t d) (offsetCellValueList_nodup t d) cell
  have hneighborCount := lawful_count_eq_indicator_of_nodup
    (offsetCellValueList t d) (offsetCellValueList_nodup t d)
      (neighboringCell cell .side₅)
  rw [hcellCount, hneighborCount]
  by_cases hcell : inBenzel (t + 2) (offsetB t d) cell <;>
    by_cases hneighbor : inBenzel (t + 2) (offsetB t d)
      (neighboringCell cell .side₅) <;>
    simp [mem_offsetCellValueList_iff, hcell, hneighbor]

theorem classMinusOneOffsetParameters
    (s r : ℕ) (hs : 1 ≤ s) :
    (2 * s + r - 1 + 2 = 2 * s + r + 1) ∧
      offsetB (2 * s + r - 1) (3 * s + 1) = s + 2 * r + 1 := by
  unfold offsetB
  constructor <;> omega

theorem directedEdgeCoefficient_classMinusOneBoundary_sideFive
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [directedEdgeCoefficient,
    cmoLiteralBoundaryWalk_forward_count,
    cmoLiteralBoundaryWalk_reverse_count,
    cmoWalkSideFiveCell_count_difference s r hs,
    offsetCellBoundaryCoefficient_sideFive]
  have hp := classMinusOneOffsetParameters s r hs
  rw [hp.1, hp.2]
  by_cases hcell :
      inBenzel (2 * s + r + 1) (s + 2 * r + 1) cell <;>
    by_cases hneighbor :
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (neighboringCell cell .side₅) <;>
    simp [mem_cmoSideFiveCells_iff s r hs,
      mem_cmoSideFiveNegativeCells_iff s r hs,
      hcell, hneighbor]

end FiniteDefects
