import D4KernelOnly.D4BoundaryRotation

/-! # All six directed boundary coefficients for the physical d=4 walk -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

def d4RotateCell (cell : Cell) : Cell :=
  (cell.2, 1 - cell.1 - cell.2)

theorem d4RotateVertex_injective : Function.Injective d4RotateVertex := by
  rintro ⟨x, y⟩ ⟨u, v⟩ h
  simp [d4RotateVertex] at h
  apply Prod.ext <;> omega

theorem d4RotateLabel_injective : Function.Injective d4RotateLabel := by
  intro left right h
  cases left <;> cases right <;> simp_all [d4RotateLabel]

theorem d4RotateEdge_injective : Function.Injective d4RotateEdge := by
  intro left right h
  apply labeledHexEdge_ext
  · exact d4RotateVertex_injective (congrArg LabeledHexEdge.source h)
  · exact d4RotateVertex_injective (congrArg LabeledHexEdge.target h)
  · exact d4RotateLabel_injective (congrArg LabeledHexEdge.label h)

theorem d4RotateEdge_reverse (edge : LabeledHexEdge) :
    d4RotateEdge (reverseLabeledHexEdge edge) =
      reverseLabeledHexEdge (d4RotateEdge edge) := by
  rfl

theorem d4RotateCell_three (cell : Cell) :
    d4RotateCell (d4RotateCell (d4RotateCell cell)) = cell := by
  rcases cell with ⟨i, j⟩
  apply Prod.ext <;> simp [d4RotateCell] <;> ring

theorem d4RotateCell_injective : Function.Injective d4RotateCell := by
  intro left right h
  have := congrArg (fun cell => d4RotateCell (d4RotateCell cell)) h
  simpa [d4RotateCell_three] using this

theorem inBenzel_d4RotateCell_iff (a b : ℕ) (cell : Cell) :
    inBenzel a b (d4RotateCell cell) ↔ inBenzel a b cell := by
  rcases cell with ⟨i, j⟩
  simp [inBenzel, d4RotateCell]
  constructor <;> rintro ⟨h0, h1, h2, h3, h4, h5⟩
  · exact ⟨h4, h5, h0, h1, h2, h3⟩
  · exact ⟨h2, h3, h4, h5, h0, h1⟩

theorem d4RotateCell_neighbor_sideFive (cell : Cell) :
    d4RotateCell (neighboringCell cell .side₅) =
      neighboringCell (d4RotateCell cell) .side₃ := by
  rcases cell with ⟨i, j⟩
  apply Prod.ext <;> simp [d4RotateCell, neighboringCell] <;> ring

theorem d4RotateCell_neighbor_sideThree (cell : Cell) :
    d4RotateCell (neighboringCell cell .side₃) =
      neighboringCell (d4RotateCell cell) .side₁ := by
  rcases cell with ⟨i, j⟩
  apply Prod.ext <;> simp [d4RotateCell, neighboringCell] <;> ring

theorem d4RotateEdge_cell_sideFive (cell : Cell) :
    d4RotateEdge (cellBoundaryEdgeAt cell .side₅) =
      cellBoundaryEdgeAt (d4RotateCell cell) .side₃ := by
  rcases cell with ⟨i, j⟩
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4RotateEdge, d4RotateVertex, d4RotateCell,
      cellBoundaryEdgeAt, hexCellStartVertex, hexCellCenter,
      advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
      ShadowStep.neg] <;> ring
  · apply Prod.ext <;> simp [d4RotateEdge, d4RotateVertex, d4RotateCell,
      cellBoundaryEdgeAt, hexCellStartVertex, hexCellCenter,
      advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
      ShadowStep.neg] <;> ring
  · rfl

theorem d4RotateEdge_cell_sideThree (cell : Cell) :
    d4RotateEdge (cellBoundaryEdgeAt cell .side₃) =
      cellBoundaryEdgeAt (d4RotateCell cell) .side₁ := by
  rcases cell with ⟨i, j⟩
  apply labeledHexEdge_ext
  · apply Prod.ext <;> simp [d4RotateEdge, d4RotateVertex, d4RotateCell,
      cellBoundaryEdgeAt, hexCellStartVertex, hexCellCenter,
      advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
      ShadowStep.neg] <;> ring
  · apply Prod.ext <;> simp [d4RotateEdge, d4RotateVertex, d4RotateCell,
      cellBoundaryEdgeAt, hexCellStartVertex, hexCellCenter,
      advanceLabeledHexEdge, addHexStep, shadowA, shadowB, shadowC,
      ShadowStep.neg] <;> ring
  · rfl

theorem directedEdgeCoefficient_reverse_target
    (edges : List LabeledHexEdge) (edge : LabeledHexEdge) :
    directedEdgeCoefficient edges (reverseLabeledHexEdge edge) =
      -directedEdgeCoefficient edges edge := by
  simp [directedEdgeCoefficient, reverseLabeledHexEdge_involutive]

theorem d4LiteralBoundaryWalk_coefficient_rotate
    (m : ℕ) (edge : LabeledHexEdge) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (d4RotateEdge edge) =
      directedEdgeCoefficient (d4LiteralBoundaryWalk m) edge := by
  have hperm := d4LiteralBoundaryWalk_rotate_perm m
  have hforward := lawful_count_map_of_injective
    (d4LiteralBoundaryWalk m) d4RotateEdge d4RotateEdge_injective edge
  have hreverse := lawful_count_map_of_injective
    (d4LiteralBoundaryWalk m) d4RotateEdge d4RotateEdge_injective
      (reverseLabeledHexEdge edge)
  rw [d4RotateEdge_reverse] at hreverse
  unfold directedEdgeCoefficient
  rw [← hperm.count_eq (d4RotateEdge edge), hforward,
    ← hperm.count_eq (reverseLabeledHexEdge (d4RotateEdge edge)), hreverse]

theorem directedEdgeCoefficient_d4CellBoundaries
    (m : ℕ) (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell side) =
      (if inBenzel (m + 4) (2 * m + 4) cell then (1 : ℤ) else 0) -
        (if inBenzel (m + 4) (2 * m + 4)
          (neighboringCell cell side) then (1 : ℤ) else 0) := by
  rw [directedEdgeCoefficient_orientedCellBoundaryList]
  have hcellCount := lawful_count_eq_indicator_of_nodup
    (d4CellValueList m) (d4CellValueList_nodup m) cell
  have hneighborCount := lawful_count_eq_indicator_of_nodup
    (d4CellValueList m) (d4CellValueList_nodup m)
      (neighboringCell cell side)
  rw [hcellCount, hneighborCount]
  simp only [mem_d4CellValueList_iff]
  by_cases hcell : inBenzel (m + 4) (2 * m + 4) cell <;>
    by_cases hneighbor : inBenzel (m + 4) (2 * m + 4)
      (neighboringCell cell side) <;> simp [hcell, hneighbor]

theorem d4CellBoundaryCoefficient_rotate_sideFive
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [directedEdgeCoefficient_d4CellBoundaries,
    directedEdgeCoefficient_d4CellBoundaries,
    ← d4RotateCell_neighbor_sideFive]
  simp only [inBenzel_d4RotateCell_iff]

theorem d4CellBoundaryCoefficient_rotate_sideThree
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₃) := by
  rw [directedEdgeCoefficient_d4CellBoundaries,
    directedEdgeCoefficient_d4CellBoundaries,
    ← d4RotateCell_neighbor_sideThree]
  simp only [inBenzel_d4RotateCell_iff]

theorem directedEdgeCoefficient_d4LiteralBoundaryWalk_sideThree_rotated
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₃) := by
  calc
    _ = directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₅)) := by
      rw [d4RotateEdge_cell_sideFive]
    _ = directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt cell .side₅) :=
      d4LiteralBoundaryWalk_coefficient_rotate m _
    _ = directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₅) :=
      directedEdgeCoefficient_d4LiteralBoundaryWalk_sideFive m cell
    _ = _ := (d4CellBoundaryCoefficient_rotate_sideFive m cell).symm

theorem directedEdgeCoefficient_d4LiteralBoundaryWalk_sideThree
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt cell .side₃) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₃) := by
  have h := directedEdgeCoefficient_d4LiteralBoundaryWalk_sideThree_rotated
    m (d4RotateCell (d4RotateCell cell))
  simpa [d4RotateCell_three] using h

theorem directedEdgeCoefficient_d4LiteralBoundaryWalk_sideOne_rotated
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt (d4RotateCell cell) .side₁) := by
  calc
    _ = directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₃)) := by
      rw [d4RotateEdge_cell_sideThree]
    _ = directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt cell .side₃) :=
      d4LiteralBoundaryWalk_coefficient_rotate m _
    _ = directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₃) :=
      directedEdgeCoefficient_d4LiteralBoundaryWalk_sideThree m cell
    _ = _ := (d4CellBoundaryCoefficient_rotate_sideThree m cell).symm

theorem directedEdgeCoefficient_d4LiteralBoundaryWalk_sideOne
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt cell .side₁) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₁) := by
  have h := directedEdgeCoefficient_d4LiteralBoundaryWalk_sideOne_rotated
    m (d4RotateCell (d4RotateCell cell))
  simpa [d4RotateCell_three] using h

theorem directedEdgeCoefficient_d4LiteralBoundaryWalk_even
    (m : ℕ) (cell : Cell) (side : HexSide)
    (heven : side = .side₀ ∨ side = .side₂ ∨ side = .side₄) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell side) := by
  rcases heven with rfl | rfl | rfl
  · have h := directedEdgeCoefficient_d4LiteralBoundaryWalk_sideThree m
      (neighboringCell cell .side₀)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₀
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h
  · have h := directedEdgeCoefficient_d4LiteralBoundaryWalk_sideFive m
      (neighboringCell cell .side₂)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₂
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h
  · have h := directedEdgeCoefficient_d4LiteralBoundaryWalk_sideOne m
      (neighboringCell cell .side₄)
    have hedge := cellBoundaryEdgeAt_neighbor_exact cell .side₄
    simp only [oppositeHexSide] at hedge
    rw [hedge, directedEdgeCoefficient_reverse_target,
      directedEdgeCoefficient_reverse_target] at h
    exact neg_inj.mp h

theorem directedEdgeCoefficient_d4LiteralBoundaryWalk_allSides
    (m : ℕ) (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell side) := by
  cases side
  · exact directedEdgeCoefficient_d4LiteralBoundaryWalk_even m cell .side₀
      (Or.inl rfl)
  · exact directedEdgeCoefficient_d4LiteralBoundaryWalk_sideOne m cell
  · exact directedEdgeCoefficient_d4LiteralBoundaryWalk_even m cell .side₂
      (Or.inr (Or.inl rfl))
  · exact directedEdgeCoefficient_d4LiteralBoundaryWalk_sideThree m cell
  · exact directedEdgeCoefficient_d4LiteralBoundaryWalk_even m cell .side₄
      (Or.inr (Or.inr rfl))
  · exact directedEdgeCoefficient_d4LiteralBoundaryWalk_sideFive m cell

end FiniteDefects
