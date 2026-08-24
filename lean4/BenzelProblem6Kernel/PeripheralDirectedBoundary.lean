import BenzelProblem6Kernel.PeripheralSide2Incidences

/-! # Directed coefficients of the literal peripheral boundary -/

namespace BenzelProblem6Kernel

theorem cellSideBoundaryEdge_injective :
    Function.Injective cellSideBoundaryEdge := by
  rintro ⟨leftCell, leftSide⟩ ⟨rightCell, rightSide⟩ hedge
  apply Prod.ext
  · exact ((cellBoundaryEdgeAt_eq_iff leftCell rightCell
      leftSide rightSide).mp hedge.symm).1.symm
  · exact ((cellBoundaryEdgeAt_eq_iff leftCell rightCell
      leftSide rightSide).mp hedge.symm).2.symm

theorem cellBoundaryEdgeAt_mem_literalReducedPeripheralBoundary_iff
    (m : ℕ) (cell : Cell) (side : HexSide) :
    cellBoundaryEdgeAt cell side ∈ literalReducedPeripheralBoundary m ↔
      IsInsidePeripheralEdge m cell side := by
  simp only [literalReducedPeripheralBoundary, List.mem_map,
    List.mem_reverse]
  constructor
  · rintro ⟨datum, hdatum, hedge⟩
    have heq := (cellBoundaryEdgeAt_eq_iff cell datum.1 side datum.2).mp
      hedge
    have hdatumEq : datum = (cell, side) := by
      exact Prod.ext heq.1 heq.2
    subst datum
    exact (isInsidePeripheralEdge_iff_mem m cell side).mpr hdatum
  · intro hins
    refine ⟨(cell, side),
      (isInsidePeripheralEdge_iff_mem m cell side).mp hins, rfl⟩

theorem count_cellSideBoundaryEdge_literalReducedPeripheralBoundary
    (m : ℕ) (datum : CellSide) :
    (literalReducedPeripheralBoundary m).count
        (cellSideBoundaryEdge datum) =
      (literalPeripheralIncidences m).countP
        (fun candidate => candidate == datum) := by
  simp only [literalReducedPeripheralBoundary, List.map_reverse,
    List.count_reverse, List.count_eq_countP, List.countP_reverse,
    List.countP_map,
    Function.comp_apply]
  apply List.countP_congr
  intro candidate hcandidate
  change (cellSideBoundaryEdge candidate == cellSideBoundaryEdge datum) = true ↔
    (candidate == datum) = true
  rw [cellSideBoundaryEdge_injective.beq_eq]

theorem count_side₅Edge_literalReducedPeripheralBoundary
    (m : ℕ) (cell : Cell) :
    (literalReducedPeripheralBoundary m).count
        (cellBoundaryEdgeAt cell .side₅) =
      if IsInsidePeripheralEdge m cell .side₅ then 1 else 0 := by
  rw [← show cellSideBoundaryEdge (cell, .side₅) =
      cellBoundaryEdgeAt cell .side₅ by rfl,
    count_cellSideBoundaryEdge_literalReducedPeripheralBoundary]
  have hfilter :
      (literalPeripheralIncidences m).countP
          (fun candidate => candidate == (cell, .side₅)) =
        (literalPeripheralSide₅Incidences m).countP
          (fun candidate => candidate == (cell, .side₅)) := by
    rw [literalPeripheralSide₅Incidences, List.countP_filter]
    apply (List.countP_congr (l := literalPeripheralIncidences m))
    intro candidate hcandidate
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h
      exact ⟨h, by simp [h]⟩
    · exact fun h => h.1
  rw [hfilter]
  rw [lawful_countP_eq_indicator_of_nodup
    (literalPeripheralSide₅Incidences m)
    (literalPeripheralSide₅Incidences_nodup m) (cell, .side₅)]
  have hmem :
      (cell, .side₅) ∈ literalPeripheralSide₅Incidences m ↔
        IsInsidePeripheralEdge m cell .side₅ := by
    simp [literalPeripheralSide₅Incidences,
      ← isInsidePeripheralEdge_iff_mem]
  by_cases h : IsInsidePeripheralEdge m cell .side₅ <;>
    simp [h, hmem]

theorem count_reverseSide₅Edge_literalReducedPeripheralBoundary
    (m : ℕ) (cell : Cell) :
    (literalReducedPeripheralBoundary m).count
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) =
      if IsInsidePeripheralEdge m
          (neighboringCell cell .side₅) .side₂ then 1 else 0 := by
  have hedge :
      reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅) =
        cellBoundaryEdgeAt (neighboringCell cell .side₅) .side₂ := by
    simpa [oppositeHexSide] using
      (cellBoundaryEdgeAt_neighbor_exact cell .side₅).symm
  rw [hedge]
  rw [← show cellSideBoundaryEdge
      (neighboringCell cell .side₅, .side₂) =
        cellBoundaryEdgeAt (neighboringCell cell .side₅) .side₂ by rfl,
    count_cellSideBoundaryEdge_literalReducedPeripheralBoundary]
  have hfilter :
      (literalPeripheralIncidences m).countP
          (fun candidate => candidate ==
            (neighboringCell cell .side₅, .side₂)) =
        (literalPeripheralSide₂Incidences m).countP
          (fun candidate => candidate ==
            (neighboringCell cell .side₅, .side₂)) := by
    rw [literalPeripheralSide₂Incidences, List.countP_filter]
    apply (List.countP_congr (l := literalPeripheralIncidences m))
    intro candidate hcandidate
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h
      exact ⟨h, by simp [h]⟩
    · exact fun h => h.1
  rw [hfilter]
  rw [lawful_countP_eq_indicator_of_nodup
    (literalPeripheralSide₂Incidences m)
    (literalPeripheralSide₂Incidences_nodup m)
      (neighboringCell cell .side₅, .side₂)]
  have hmem :
      (neighboringCell cell .side₅, .side₂) ∈
          literalPeripheralSide₂Incidences m ↔
        IsInsidePeripheralEdge m
          (neighboringCell cell .side₅) .side₂ := by
    simp [literalPeripheralSide₂Incidences,
      ← isInsidePeripheralEdge_iff_mem]
  by_cases h : IsInsidePeripheralEdge m
      (neighboringCell cell .side₅) .side₂ <;>
    simp [h, hmem]

theorem directedEdgeCoefficient_literalReducedPeripheralBoundary_side₅
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (literalReducedPeripheralBoundary m)
        (cellBoundaryEdgeAt cell .side₅) =
      (if inPeripheralBenzel (m + 5) cell then (1 : ℤ) else 0) -
        (if inPeripheralBenzel (m + 5)
          (neighboringCell cell .side₅) then (1 : ℤ) else 0) := by
  rw [directedEdgeCoefficient,
    count_side₅Edge_literalReducedPeripheralBoundary,
    count_reverseSide₅Edge_literalReducedPeripheralBoundary]
  have hback : neighboringCell
      (neighboringCell cell .side₅) .side₂ = cell := by
    exact neighboringCell_opposite cell .side₅
  simp only [IsInsidePeripheralEdge, hback]
  by_cases hcell : inPeripheralBenzel (m + 5) cell <;>
    by_cases hneighbor : inPeripheralBenzel (m + 5)
      (neighboringCell cell .side₅) <;> simp [hcell, hneighbor]

theorem directedEdgeCoefficient_benzelCellBoundaries_side₅
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList (benzelCellValueList m))
        (cellBoundaryEdgeAt cell .side₅) =
      (if inPeripheralBenzel (m + 5) cell then (1 : ℤ) else 0) -
        (if inPeripheralBenzel (m + 5)
          (neighboringCell cell .side₅) then (1 : ℤ) else 0) := by
  rw [directedEdgeCoefficient_orientedCellBoundaryList]
  have hcellCount := lawful_count_eq_indicator_of_nodup
    (benzelCellValueList m) (benzelCellValueList_nodup m) cell
  have hneighborCount := lawful_count_eq_indicator_of_nodup
    (benzelCellValueList m) (benzelCellValueList_nodup m)
      (neighboringCell cell .side₅)
  rw [hcellCount, hneighborCount]
  by_cases hcell : inPeripheralBenzel (m + 5) cell <;>
    by_cases hneighbor : inPeripheralBenzel (m + 5)
      (neighboringCell cell .side₅) <;>
      simp [mem_benzelCellValueList_iff, hcell, hneighbor]

theorem literalReducedBoundary_eq_tilingBoundaryCoefficient_side₅
    {m : ℕ} (tiling : LiteralTiling m) (cell : Cell) :
    directedEdgeCoefficient (literalReducedPeripheralBoundary m)
        (cellBoundaryEdgeAt cell .side₅) =
      directedEdgeCoefficient
        (literalPlacementBoundaryList tiling.1.toList)
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [directedEdgeCoefficient_literalReducedPeripheralBoundary_side₅,
    ← directedEdgeCoefficient_benzelCellBoundaries_side₅]
  exact (literalTilingPlacementBoundaries_eq_benzelCellBoundaries
    tiling (cellBoundaryEdgeAt cell .side₅)).symm

end BenzelProblem6Kernel
