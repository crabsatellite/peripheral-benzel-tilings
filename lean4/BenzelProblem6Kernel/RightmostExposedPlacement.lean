import BenzelProblem6Kernel.ExposedPlacementEdgeComplete
import Mathlib.Data.Finset.Max

/-!
# A nonempty finite placement family has a rightmost exposed edge

No connectivity or convexity is needed.  Maximize the first coordinate over
all covered cells.  Its positive first-coordinate neighbor is uncovered, so
the exact oriented `side₅` edge lies on the boundary of the unique placement
that owns the selected cell.
-/

namespace BenzelProblem6Kernel

def placementUnionCells {m : ℕ}
    (placements : Finset (LiteralPlacement m)) : Finset Cell :=
  placements.biUnion fun placement => placement.cells.toFinset

theorem placement_base_mem_cells {m : ℕ}
    (placement : LiteralPlacement m) :
    placement.base ∈ placement.cells := by
  change placement.base ∈
    (protoCells placement.tile).map
      (translateLocalCell placement.base)
  cases placement.tile <;>
    simp [protoCells, translateLocalCell, c00]

theorem placementUnionCells_nonempty {m : ℕ}
    {placements : Finset (LiteralPlacement m)}
    (hplacements : placements.Nonempty) :
    (placementUnionCells placements).Nonempty := by
  obtain ⟨placement, hplacement⟩ := hplacements
  refine ⟨placement.base, ?_⟩
  rw [placementUnionCells, Finset.mem_biUnion]
  exact ⟨placement, hplacement, List.mem_toFinset.mpr
    (placement_base_mem_cells placement)⟩

theorem exists_rightmost_union_cell {m : ℕ}
    {placements : Finset (LiteralPlacement m)}
    (hplacements : placements.Nonempty) :
    ∃ cell ∈ placementUnionCells placements,
      ∀ other ∈ placementUnionCells placements,
        other.1 ≤ cell.1 := by
  exact Finset.exists_max_image (placementUnionCells placements)
    Prod.fst (placementUnionCells_nonempty hplacements)

theorem rightmost_side₅_neighbor_not_mem {m : ℕ}
    {placements : Finset (LiteralPlacement m)} {cell : Cell}
    (hmax : ∀ other ∈ placementUnionCells placements,
      other.1 ≤ cell.1) :
    neighboringCell cell .side₅ ∉ placementUnionCells placements := by
  intro hneighbor
  have hle := hmax (neighboringCell cell .side₅) hneighbor
  rcases cell with ⟨i, j⟩
  simp [neighboringCell] at hle

theorem exists_rightmost_exposed_placement {m : ℕ}
    {placements : Finset (LiteralPlacement m)}
    (hplacements : placements.Nonempty) :
    ∃ placement ∈ placements, ∃ cell ∈ placement.cells,
      neighboringCell cell .side₅ ∉ placementUnionCells placements ∧
        cellBoundaryEdgeAt cell .side₅ ∈
          literalPlacementBoundary placement := by
  obtain ⟨cell, hcellUnion, hmax⟩ :=
    exists_rightmost_union_cell hplacements
  rw [placementUnionCells, Finset.mem_biUnion] at hcellUnion
  obtain ⟨placement, hplacement, hcell⟩ := hcellUnion
  have hneighbor := rightmost_side₅_neighbor_not_mem hmax
  have hneighborPlacement :
      neighboringCell cell .side₅ ∉ placement.cells := by
    intro hmem
    apply hneighbor
    rw [placementUnionCells, Finset.mem_biUnion]
    exact ⟨placement, hplacement, List.mem_toFinset.mpr hmem⟩
  exact ⟨placement, hplacement, cell, List.mem_toFinset.mp hcell,
    hneighbor, exposed_side₅_mem_literalPlacementBoundary
      placement cell (List.mem_toFinset.mp hcell) hneighborPlacement⟩

end BenzelProblem6Kernel
