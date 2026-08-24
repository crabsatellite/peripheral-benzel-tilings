import BenzelProblem6Kernel.HexCellEdgeIncidenceComplete

/-!
# Boundary parity for a literal benzel cell list

Unique edge incidence reduces membership in the XOR of cell boundaries to one
Boolean condition: exactly one of the two adjacent cells belongs to the
region.
-/

namespace BenzelProblem6Kernel

open scoped symmDiff

theorem mem_cellBoundaryKeys_iff_exists_side
    (key : LabeledHexEdgeKey) (cell : Cell) :
    key ∈ cellBoundaryKeys cell ↔
      ∃ side : HexSide, (cellBoundaryEdgeAt cell side).key = key := by
  rw [cellBoundaryKeys, labeledBoundaryKeys,
    labeledCellBoundary_eq_allEdges]
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨edge, hedge, hkey⟩
    simp [allCellBoundaryEdges] at hedge
    rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.side₀, hkey⟩
    · exact ⟨.side₁, hkey⟩
    · exact ⟨.side₂, hkey⟩
    · exact ⟨.side₃, hkey⟩
    · exact ⟨.side₄, hkey⟩
    · exact ⟨.side₅, hkey⟩
  · rintro ⟨side, hkey⟩
    refine ⟨cellBoundaryEdgeAt cell side, ?_, hkey⟩
    cases side <;> simp [allCellBoundaryEdges]

theorem cellBoundaryEdgeAt_key_mem_cell_iff
    (leftCell rightCell : Cell) (leftSide : HexSide) :
    (cellBoundaryEdgeAt leftCell leftSide).key ∈
        cellBoundaryKeys rightCell ↔
      rightCell = leftCell ∨
        rightCell = neighboringCell leftCell leftSide := by
  rw [mem_cellBoundaryKeys_iff_exists_side]
  constructor
  · rintro ⟨rightSide, hkey⟩
    have hincidence := (cellBoundaryEdgeAt_key_eq_iff
      leftCell rightCell leftSide rightSide).mp hkey.symm
    exact hincidence.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · rintro (rfl | rfl)
    · exact ⟨leftSide, rfl⟩
    · exact ⟨oppositeHexSide leftSide,
        (cellBoundaryEdgeAt_neighbor leftCell leftSide).symm⟩

theorem cellBoundaryEdgeAt_key_mem_xor_iff
    (cells : List Cell) (hnodup : cells.Nodup)
    (leftCell : Cell) (leftSide : HexSide) :
    (cellBoundaryEdgeAt leftCell leftSide).key ∈
        xorCellBoundaryList cells ↔
      (leftCell ∈ cells ∧ neighboringCell leftCell leftSide ∉ cells) ∨
        (neighboringCell leftCell leftSide ∈ cells ∧
          leftCell ∉ cells) := by
  induction cells with
  | nil =>
      simp [xorCellBoundaryList, Finset.mem_symmDiff]
  | cons head tail ih =>
      have hcons := List.nodup_cons.mp hnodup
      simp only [xorCellBoundaryList, Finset.mem_symmDiff,
        cellBoundaryEdgeAt_key_mem_cell_iff,
        ih hcons.2, List.mem_cons]
      have hneighborRight := neighboringCell_ne leftCell leftSide
      have hneighborLeft :
          leftCell ≠ neighboringCell leftCell leftSide := hneighborRight.symm
      by_cases hleft : head = leftCell
      · subst head
        simp [hcons.1, hneighborLeft, hneighborRight]
      · by_cases hright : head = neighboringCell leftCell leftSide
        · subst head
          simp [hcons.1, hneighborLeft, hneighborRight]
        · simp [hleft, Ne.symm hleft, hright, Ne.symm hright]

theorem cellBoundaryEdgeAt_key_mem_benzelXor_iff
    (m : ℕ) (cell : Cell) (side : HexSide) :
    (cellBoundaryEdgeAt cell side).key ∈
        xorCellBoundaryList (benzelCellValueList m) ↔
      (inPeripheralBenzel (m + 5) cell ∧
          ¬inPeripheralBenzel (m + 5) (neighboringCell cell side)) ∨
        (inPeripheralBenzel (m + 5) (neighboringCell cell side) ∧
          ¬inPeripheralBenzel (m + 5) cell) := by
  rw [cellBoundaryEdgeAt_key_mem_xor_iff
    (benzelCellValueList m) (benzelCellValueList_nodup m)]
  simp only [mem_benzelCellValueList_iff]

end BenzelProblem6Kernel
