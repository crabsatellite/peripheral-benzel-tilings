import D4KernelOnly.GeneralEnergyDoubleCount
import Mathlib.Data.Fintype.Card

/-! # Exact-cover incidence count for every literal offset benzel -/

namespace FiniteDefects

theorem offset_tiling_card_mul_three {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    tiling.1.card * 3 = Fintype.card (OffsetCell t d) := by
  classical
  calc
    tiling.1.card * 3 =
        ∑ placement ∈ tiling.1, (offsetPlacementCells placement).card := by
      simp [card_offsetPlacementCells]
    _ = ∑ cell : OffsetCell t d,
          (tiling.1.filter fun placement =>
            OffsetPlacementCovers placement cell).card := by
      calc
        (∑ placement ∈ tiling.1, (offsetPlacementCells placement).card) =
            ∑ placement ∈ tiling.1,
              ∑ cell : OffsetCell t d,
                if OffsetPlacementCovers placement cell then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro placement _
          have hfilter :
              Finset.univ.filter (fun cell : OffsetCell t d =>
                OffsetPlacementCovers placement cell) =
                offsetPlacementCells placement := by
            ext cell
            simp [mem_offsetPlacementCells_iff]
          rw [← hfilter, Finset.card_filter]
        _ = ∑ cell : OffsetCell t d,
              ∑ placement ∈ tiling.1,
                if OffsetPlacementCovers placement cell then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro cell _
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = Fintype.card (OffsetCell t d) := by
      have hcard (cell : OffsetCell t d) :
          (tiling.1.filter fun placement =>
            OffsetPlacementCovers placement cell).card = 1 := by
        obtain ⟨placement, hplacement⟩ :=
          offset_exact_cover_filter_singleton tiling cell
        rw [hplacement]
        simp
      simp_rw [hcard]
      simp

end FiniteDefects
