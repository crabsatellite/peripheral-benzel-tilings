import BenzelProblem6Kernel.LiteralPeripheralIncidenceComplete

/-!
# Exact peripheral boundary keys

The arithmetic incidence list is converted to literal labeled edges.  Its key
finset is proved extensionally equal to the XOR of every benzel-cell boundary.
-/

namespace BenzelProblem6Kernel

def cellSideBoundaryEdge (datum : CellSide) : LabeledHexEdge :=
  cellBoundaryEdgeAt datum.1 datum.2

def cellSideBoundaryKey (datum : CellSide) : LabeledHexEdgeKey :=
  (cellSideBoundaryEdge datum).key

def literalPeripheralBoundaryKeyFinset (m : ℕ) :
    Finset LabeledHexEdgeKey :=
  (literalPeripheralIncidences m).toFinset.image cellSideBoundaryKey

def literalReducedPeripheralBoundary (m : ℕ) :
    List LabeledHexEdge :=
  (literalPeripheralIncidences m).reverse.map cellSideBoundaryEdge

theorem mem_xorCellBoundaryList_exists_cell
    {key : LabeledHexEdgeKey} {cells : List Cell}
    (hkey : key ∈ xorCellBoundaryList cells) :
    ∃ cell ∈ cells, key ∈ cellBoundaryKeys cell := by
  induction cells with
  | nil => simp [xorCellBoundaryList] at hkey
  | cons cell rest ih =>
      rw [xorCellBoundaryList, Finset.mem_symmDiff] at hkey
      rcases hkey with ⟨hcell, _⟩ | ⟨hrest, _⟩
      · exact ⟨cell, by simp, hcell⟩
      · obtain ⟨owner, howner, hownerKey⟩ := ih hrest
        exact ⟨owner, by simp [howner], hownerKey⟩

theorem literalPeripheralBoundaryKeyFinset_eq_benzelXor (m : ℕ) :
    literalPeripheralBoundaryKeyFinset m =
      xorCellBoundaryList (benzelCellValueList m) := by
  ext key
  constructor
  · intro hkey
    simp only [literalPeripheralBoundaryKeyFinset, Finset.mem_image,
      List.mem_toFinset] at hkey
    obtain ⟨datum, hdatum, rfl⟩ := hkey
    have hins := (isInsidePeripheralEdge_iff_mem
      m datum.1 datum.2).mpr hdatum
    exact (cellBoundaryEdgeAt_key_mem_benzelXor_iff
      m datum.1 datum.2).mpr (Or.inl hins)
  · intro hkey
    obtain ⟨cell, hcell, hcellKey⟩ :=
      mem_xorCellBoundaryList_exists_cell hkey
    obtain ⟨side, hside⟩ :=
      (mem_cellBoundaryKeys_iff_exists_side key cell).mp hcellKey
    have hedgeKey :
        (cellBoundaryEdgeAt cell side).key ∈
          xorCellBoundaryList (benzelCellValueList m) := by
      rwa [hside]
    have hparity := (cellBoundaryEdgeAt_key_mem_benzelXor_iff
      m cell side).mp hedgeKey
    simp only [literalPeripheralBoundaryKeyFinset, Finset.mem_image,
      List.mem_toFinset]
    rcases hparity with hins | hins
    · have hdatum := (isInsidePeripheralEdge_iff_mem
        m cell side).mp hins
      exact ⟨(cell, side), hdatum, hside⟩
    · let neighbor := neighboringCell cell side
      let opposite := oppositeHexSide side
      have hinsideNeighbor : IsInsidePeripheralEdge m neighbor opposite := by
        constructor
        · exact hins.1
        · simpa [neighbor, opposite, neighboringCell_opposite] using hins.2
      have hdatum := (isInsidePeripheralEdge_iff_mem
        m neighbor opposite).mp hinsideNeighbor
      refine ⟨(neighbor, opposite), hdatum, ?_⟩
      exact (cellBoundaryEdgeAt_neighbor cell side).symm.trans hside

theorem literalReducedPeripheralBoundary_keys (m : ℕ) :
    labeledBoundaryKeys (literalReducedPeripheralBoundary m) =
      literalPeripheralBoundaryKeyFinset m := by
  ext key
  simp [labeledBoundaryKeys, literalReducedPeripheralBoundary,
    literalPeripheralBoundaryKeyFinset, cellSideBoundaryKey,
    cellSideBoundaryEdge]
  aesop

theorem literalReducedPeripheralBoundary_keys_eq_benzelXor (m : ℕ) :
    labeledBoundaryKeys (literalReducedPeripheralBoundary m) =
      xorCellBoundaryList (benzelCellValueList m) := by
  rw [literalReducedPeripheralBoundary_keys,
    literalPeripheralBoundaryKeyFinset_eq_benzelXor]

end BenzelProblem6Kernel
