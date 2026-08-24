import BenzelProblem6Kernel.PhaseLocalEnergy
import BenzelProblem6Kernel.TilingIncidence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weighted incidence double count for literal tilings

The unweighted incidence theorem counts cells.  Here the same exact-cover
partition is weighted by the unique periodic-owner energy of each cell.  This
identifies the literal sum of the local tile table with the already checked
global benzel energy.
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

theorem placement_literal_cell_energy_sum {m : ℕ}
    (placement : LiteralPlacement m) :
    ∑ cell ∈ placementBenzelCells placement,
        literalCellEnergy (by omega : 5 ≤ m + 5) cell =
      literalPlacementEnergy placement := by
  classical
  calc
    (∑ cell ∈ placementBenzelCells placement,
        literalCellEnergy (by omega : 5 ≤ m + 5) cell) =
        ∑ attached ∈ placement.cells.toFinset.attach,
          literalCellEnergy (by omega : 5 ≤ m + 5)
            (placementCellEmbedding placement attached) := by
      rw [placementBenzelCells, Finset.sum_map]
    _ = ∑ rawCell ∈ placement.cells.toFinset,
          phaseCellEnergy (m + 3) rawCell := by
      conv_rhs => rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro attached _
      rw [literalCellEnergy_eq_phaseCellEnergy]
      rfl
    _ = (placement.cells.map (phaseCellEnergy (m + 3))).sum := by
      exact List.sum_toFinset (phaseCellEnergy (m + 3))
        (placementCellList_nodup placement.1)
    _ = literalPlacementEnergy placement :=
      phase_energy_sum_of_placement placement

theorem tiling_energy_double_count {m : ℕ} (tiling : LiteralTiling m) :
    ∑ placement ∈ tiling.1, literalPlacementEnergy placement =
      ∑ cell : BenzelCell (m + 5),
        literalCellEnergy (by omega : 5 ≤ m + 5) cell := by
  classical
  calc
    (∑ placement ∈ tiling.1, literalPlacementEnergy placement) =
        ∑ placement ∈ tiling.1,
          ∑ cell ∈ placementBenzelCells placement,
            literalCellEnergy (by omega : 5 ≤ m + 5) cell := by
      apply Finset.sum_congr rfl
      intro placement _
      exact (placement_literal_cell_energy_sum placement).symm
    _ = ∑ placement ∈ tiling.1,
          ∑ cell : BenzelCell (m + 5),
            if PlacementCovers placement cell then
              literalCellEnergy (by omega : 5 ≤ m + 5) cell else 0 := by
      apply Finset.sum_congr rfl
      intro placement _
      have hfilter :
          Finset.univ.filter (fun cell : BenzelCell (m + 5) =>
            PlacementCovers placement cell) = placementBenzelCells placement := by
        ext cell
        simp [mem_placementBenzelCells_iff]
      rw [← hfilter, Finset.sum_filter]
    _ = ∑ cell : BenzelCell (m + 5),
          ∑ placement ∈ tiling.1,
            if PlacementCovers placement cell then
              literalCellEnergy (by omega : 5 ≤ m + 5) cell else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ cell : BenzelCell (m + 5),
        literalCellEnergy (by omega : 5 ≤ m + 5) cell := by
      apply Finset.sum_congr rfl
      intro cell _
      rw [← Finset.sum_filter]
      obtain ⟨placement, hplacement⟩ := exact_cover_filter_singleton tiling cell
      rw [hplacement]
      simp

theorem total_literal_tile_energy {m : ℕ} (tiling : LiteralTiling m) :
    ∑ placement ∈ tiling.1, literalPlacementEnergy placement =
      3 * ((m + 3 : ℕ) : ℤ) := by
  rw [tiling_energy_double_count]
  simpa using literal_cell_energy_sum (n := m + 5) (by omega)

end BenzelProblem6Kernel
