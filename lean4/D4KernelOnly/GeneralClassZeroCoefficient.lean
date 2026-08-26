import D4KernelOnly.GeneralClassZeroCellNodup
import D4KernelOnly.GeneralClassMinusOneCoefficient

/-! # Exact side-five coefficient identity for class-zero benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czLiteralBoundaryWalk_forward_count
    (s r : ℕ) (cell : Cell) :
    (classZeroLiteralBoundaryWalk s r).count
        (cellBoundaryEdgeAt cell .side₅) =
      (czWalkForwardSideFiveCells s r).count cell := by
  have hfilter := count_filter_eq_count_of_true
    (classZeroLiteralBoundaryWalk s r) isForwardSideFiveEdge
      (cellBoundaryEdgeAt cell .side₅)
      (isForwardSideFiveEdge_cellBoundaryEdgeAt cell)
  rw [← forwardSideFiveEdges] at hfilter
  rw [classZeroBoundaryWalk_forward,
    czWalkForwardSideFiveEdges,
    lawful_count_map_of_injective _ _
      cellBoundaryEdgeAt_sideFive_injective] at hfilter
  exact hfilter.symm

theorem czLiteralBoundaryWalk_reverse_count
    (s r : ℕ) (cell : Cell) :
    (classZeroLiteralBoundaryWalk s r).count
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) =
      (czWalkReverseSideFiveCells s r).count cell := by
  have hfilter := count_filter_eq_count_of_true
    (classZeroLiteralBoundaryWalk s r) isReverseSideFiveEdge
      (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅))
      (isReverseSideFiveEdge_reverse_cellBoundaryEdgeAt cell)
  rw [← reverseSideFiveEdges] at hfilter
  rw [classZeroBoundaryWalk_reverse,
    czWalkReverseSideFiveEdges,
    lawful_count_map_of_injective _ _
      reverse_cellBoundaryEdgeAt_sideFive_injective] at hfilter
  exact hfilter.symm

theorem czWalkSideFiveCell_count_difference
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    ((czWalkForwardSideFiveCells s r).count cell : ℤ) -
        (czWalkReverseSideFiveCells s r).count cell =
      (if cell ∈ czSideFiveCells s r then (1 : ℤ) else 0) -
        (if cell ∈ czSideFiveNegativeCells s r then (1 : ℤ) else 0) := by
  rw [lawful_count_eq_indicator_of_nodup _
      (czWalkForwardSideFiveCells_nodup s r),
    lawful_count_eq_indicator_of_nodup _
      (czWalkReverseSideFiveCells_nodup s r)]
  simp only [mem_czWalkForwardSideFiveCells_iff s r hr,
    mem_czWalkReverseSideFiveCells_iff s r hs]
  by_cases hspur : cell = czSpurCell s r
  · subst cell
    simp [czSpur_not_positive s r hs hr, czSpur_not_negative s r hs hr]
  · simp [hspur]

theorem classZeroOffsetParameters
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (2 * s + r - 2 + 2 = 2 * s + r) ∧
      offsetB (2 * s + r - 2) (3 * s) = s + 2 * r := by
  unfold offsetB
  constructor <;> omega

theorem directedEdgeCoefficient_classZeroBoundary_sideFive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [directedEdgeCoefficient,
    czLiteralBoundaryWalk_forward_count,
    czLiteralBoundaryWalk_reverse_count,
    czWalkSideFiveCell_count_difference s r hs hr,
    offsetCellBoundaryCoefficient_sideFive]
  have hp := classZeroOffsetParameters s r hs hr
  rw [hp.1, hp.2]
  by_cases hcell : inBenzel (2 * s + r) (s + 2 * r) cell <;>
    by_cases hneighbor : inBenzel (2 * s + r) (s + 2 * r)
      (neighboringCell cell .side₅) <;>
    simp [mem_czSideFiveCells_iff s r hs hr,
      mem_czSideFiveNegativeCells_iff s r hs hr,
      hcell, hneighbor]

end FiniteDefects
