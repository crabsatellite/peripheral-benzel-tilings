import D4KernelOnly.GeneralClassMinusOneRotation

/-! # All six directed boundary coefficients for class-minus-one benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem classMinusOneBoundary_coefficient_rotate
    (s r : ℕ) (edge : LabeledHexEdge) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (d4RotateEdge edge) =
      directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r) edge := by
  have hperm := classMinusOneBoundaryWalk_rotate_perm s r
  have hforward := lawful_count_map_of_injective
    (classMinusOneLiteralBoundaryWalk s r)
      d4RotateEdge d4RotateEdge_injective edge
  have hreverse := lawful_count_map_of_injective
    (classMinusOneLiteralBoundaryWalk s r)
      d4RotateEdge d4RotateEdge_injective (reverseLabeledHexEdge edge)
  rw [d4RotateEdge_reverse] at hreverse
  unfold directedEdgeCoefficient
  rw [← hperm.count_eq (d4RotateEdge edge), hforward,
    ← hperm.count_eq (reverseLabeledHexEdge (d4RotateEdge edge)), hreverse]

theorem offsetCellBoundaryCoefficient
    (t d : ℕ) (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient
        (orientedCellBoundaryList (offsetCellValueList t d))
        (cellBoundaryEdgeAt cell side) =
      (if inBenzel (t + 2) (offsetB t d) cell then (1 : ℤ) else 0) -
        (if inBenzel (t + 2) (offsetB t d)
          (neighboringCell cell side) then (1 : ℤ) else 0) := by
  rw [directedEdgeCoefficient_orientedCellBoundaryList]
  have hcellCount := lawful_count_eq_indicator_of_nodup
    (offsetCellValueList t d) (offsetCellValueList_nodup t d) cell
  have hneighborCount := lawful_count_eq_indicator_of_nodup
    (offsetCellValueList t d) (offsetCellValueList_nodup t d)
      (neighboringCell cell side)
  rw [hcellCount, hneighborCount]
  simp only [mem_offsetCellValueList_iff]
  by_cases hcell : inBenzel (t + 2) (offsetB t d) cell <;>
    by_cases hneighbor : inBenzel (t + 2) (offsetB t d)
      (neighboringCell cell side) <;> simp [hcell, hneighbor]

theorem cmoCellBoundaryCoefficient_rotate_sideFive
    (s r : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [offsetCellBoundaryCoefficient, offsetCellBoundaryCoefficient,
    ← d4RotateCell_neighbor_sideFive]
  simp only [inBenzel_d4RotateCell_iff]

theorem cmoCellBoundaryCoefficient_rotate_sideThree
    (s r : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell .side₃) := by
  rw [offsetCellBoundaryCoefficient, offsetCellBoundaryCoefficient,
    ← d4RotateCell_neighbor_sideThree]
  simp only [inBenzel_d4RotateCell_iff]

theorem directedEdgeCoefficient_cmo_sideThree_rotated
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) := by
  calc
    _ = directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₅)) := by
      rw [d4RotateEdge_cell_sideFive]
    _ = directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) :=
      classMinusOneBoundary_coefficient_rotate s r _
    _ = directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell .side₅) :=
      directedEdgeCoefficient_classMinusOneBoundary_sideFive s r hs cell
    _ = _ := (cmoCellBoundaryCoefficient_rotate_sideFive s r cell).symm

theorem directedEdgeCoefficient_cmo_sideThree
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell .side₃) := by
  have h := directedEdgeCoefficient_cmo_sideThree_rotated s r hs
    (d4RotateCell (d4RotateCell cell))
  simpa [d4RotateCell_three] using h

theorem directedEdgeCoefficient_cmo_sideOne_rotated
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) := by
  calc
    _ = directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₃)) := by
      rw [d4RotateEdge_cell_sideThree]
    _ = directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₃) :=
      classMinusOneBoundary_coefficient_rotate s r _
    _ = directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell .side₃) :=
      directedEdgeCoefficient_cmo_sideThree s r hs cell
    _ = _ := (cmoCellBoundaryCoefficient_rotate_sideThree s r cell).symm

theorem directedEdgeCoefficient_cmo_sideOne
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell .side₁) := by
  have h := directedEdgeCoefficient_cmo_sideOne_rotated s r hs
    (d4RotateCell (d4RotateCell cell))
  simpa [d4RotateCell_three] using h

theorem directedEdgeCoefficient_cmo_even
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) (side : HexSide)
    (heven : side = .side₀ ∨ side = .side₂ ∨ side = .side₄) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell side) := by
  rcases heven with rfl | rfl | rfl
  · have h := directedEdgeCoefficient_cmo_sideThree s r hs
      (neighboringCell cell .side₀)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₀
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h
  · have h := directedEdgeCoefficient_classMinusOneBoundary_sideFive
      s r hs (neighboringCell cell .side₂)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₂
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h
  · have h := directedEdgeCoefficient_cmo_sideOne s r hs
      (neighboringCell cell .side₄)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₄
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h

theorem directedEdgeCoefficient_classMinusOneBoundary_allSides
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient (classMinusOneLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell side) := by
  cases side
  · exact directedEdgeCoefficient_cmo_even s r hs cell .side₀ (Or.inl rfl)
  · exact directedEdgeCoefficient_cmo_sideOne s r hs cell
  · exact directedEdgeCoefficient_cmo_even s r hs cell .side₂
      (Or.inr (Or.inl rfl))
  · exact directedEdgeCoefficient_cmo_sideThree s r hs cell
  · exact directedEdgeCoefficient_cmo_even s r hs cell .side₄
      (Or.inr (Or.inr rfl))
  · exact directedEdgeCoefficient_classMinusOneBoundary_sideFive s r hs cell

end FiniteDefects
