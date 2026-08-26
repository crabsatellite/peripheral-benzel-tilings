import D4KernelOnly.GeneralClassZeroRotation
import D4KernelOnly.GeneralClassMinusOneAllCoefficients

/-! # All six directed boundary coefficients for class-zero benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem classZeroBoundary_coefficient_rotate
    (s r : ℕ) (edge : LabeledHexEdge) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (d4RotateEdge edge) =
      directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r) edge := by
  have hperm := classZeroBoundaryWalk_rotate_perm s r
  have hforward := lawful_count_map_of_injective
    (classZeroLiteralBoundaryWalk s r) d4RotateEdge d4RotateEdge_injective edge
  have hreverse := lawful_count_map_of_injective
    (classZeroLiteralBoundaryWalk s r) d4RotateEdge d4RotateEdge_injective
      (reverseLabeledHexEdge edge)
  rw [d4RotateEdge_reverse] at hreverse
  unfold directedEdgeCoefficient
  rw [← hperm.count_eq (d4RotateEdge edge), hforward,
    ← hperm.count_eq (reverseLabeledHexEdge (d4RotateEdge edge)), hreverse]

theorem czCellBoundaryCoefficient_rotate_sideFive
    (s r : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [offsetCellBoundaryCoefficient, offsetCellBoundaryCoefficient,
    ← d4RotateCell_neighbor_sideFive]
  simp only [inBenzel_d4RotateCell_iff]

theorem czCellBoundaryCoefficient_rotate_sideThree
    (s r : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell .side₃) := by
  rw [offsetCellBoundaryCoefficient, offsetCellBoundaryCoefficient,
    ← d4RotateCell_neighbor_sideThree]
  simp only [inBenzel_d4RotateCell_iff]

theorem directedEdgeCoefficient_cz_sideThree_rotated
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) := by
  calc
    _ = directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₅)) := by
      rw [d4RotateEdge_cell_sideFive]
    _ = directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) :=
      classZeroBoundary_coefficient_rotate s r _
    _ = directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell .side₅) :=
      directedEdgeCoefficient_classZeroBoundary_sideFive s r hs hr cell
    _ = _ := (czCellBoundaryCoefficient_rotate_sideFive s r cell).symm

theorem directedEdgeCoefficient_cz_sideThree
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell .side₃) := by
  have h := directedEdgeCoefficient_cz_sideThree_rotated s r hs hr
    (d4RotateCell (d4RotateCell cell))
  simpa [d4RotateCell_three] using h

theorem directedEdgeCoefficient_cz_sideOne_rotated
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) := by
  calc
    _ = directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₃)) := by
      rw [d4RotateEdge_cell_sideThree]
    _ = directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₃) :=
      classZeroBoundary_coefficient_rotate s r _
    _ = directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell .side₃) :=
      directedEdgeCoefficient_cz_sideThree s r hs hr cell
    _ = _ := (czCellBoundaryCoefficient_rotate_sideThree s r cell).symm

theorem directedEdgeCoefficient_cz_sideOne
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell .side₁) := by
  have h := directedEdgeCoefficient_cz_sideOne_rotated s r hs hr
    (d4RotateCell (d4RotateCell cell))
  simpa [d4RotateCell_three] using h

theorem directedEdgeCoefficient_cz_even
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (cell : Cell) (side : HexSide)
    (heven : side = .side₀ ∨ side = .side₂ ∨ side = .side₄) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell side) := by
  rcases heven with rfl | rfl | rfl
  · have h := directedEdgeCoefficient_cz_sideThree s r hs hr
      (neighboringCell cell .side₀)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₀
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h
  · have h := directedEdgeCoefficient_classZeroBoundary_sideFive
      s r hs hr (neighboringCell cell .side₂)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₂
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h
  · have h := directedEdgeCoefficient_cz_sideOne s r hs hr
      (neighboringCell cell .side₄)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₄
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h

theorem directedEdgeCoefficient_classZeroBoundary_allSides
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient (classZeroLiteralBoundaryWalk s r)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell side) := by
  cases side
  · exact directedEdgeCoefficient_cz_even s r hs hr cell .side₀ (Or.inl rfl)
  · exact directedEdgeCoefficient_cz_sideOne s r hs hr cell
  · exact directedEdgeCoefficient_cz_even s r hs hr cell .side₂
      (Or.inr (Or.inl rfl))
  · exact directedEdgeCoefficient_cz_sideThree s r hs hr cell
  · exact directedEdgeCoefficient_cz_even s r hs hr cell .side₄
      (Or.inr (Or.inr rfl))
  · exact directedEdgeCoefficient_classZeroBoundary_sideFive s r hs hr cell

end FiniteDefects
