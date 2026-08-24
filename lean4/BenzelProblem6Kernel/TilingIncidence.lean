import BenzelProblem6Kernel.LiteralTilingCarrier
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Cast.Field

/-!
# Incidence double counting for literal tilings
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

def placementCellEmbedding {m : ℕ} (placement : LiteralPlacement m) :
    {cell : Cell // cell ∈ placement.cells.toFinset} ↪ BenzelCell (m + 5) where
  toFun cell :=
    ⟨cell.1, placement.2 cell.1 (by
      have hcList : cell.1 ∈ placement.cells := by
        simpa only [List.mem_toFinset] using cell.2
      simpa [LiteralPlacement.cells] using hcList)⟩
  inj' := by
    intro left right h
    apply Subtype.ext
    exact congrArg (fun cell : BenzelCell (m + 5) => cell.1) h

def placementBenzelCells {m : ℕ} (placement : LiteralPlacement m) :
    Finset (BenzelCell (m + 5)) :=
  placement.cells.toFinset.attach.map (placementCellEmbedding placement)

theorem card_placementBenzelCells {m : ℕ} (placement : LiteralPlacement m) :
    (placementBenzelCells placement).card = 3 := by
  rw [placementBenzelCells, Finset.card_map, Finset.card_attach]
  change (placementCellList placement.1).toFinset.card = 3
  rw [List.toFinset_card_of_nodup (placementCellList_nodup placement.1)]
  exact placementCellList_length placement.1

theorem mem_placementBenzelCells_iff {m : ℕ}
    (placement : LiteralPlacement m) (cell : BenzelCell (m + 5)) :
    cell ∈ placementBenzelCells placement ↔ PlacementCovers placement cell := by
  constructor
  · intro hmem
    simp only [placementBenzelCells, Finset.mem_map, Finset.mem_attach] at hmem
    obtain ⟨attached, _, heq⟩ := hmem
    have hval := congrArg Subtype.val heq
    have hcList : attached.1 ∈ placement.cells := by
      simpa only [List.mem_toFinset] using attached.2
    unfold PlacementCovers
    simpa [← hval] using hcList
  · intro hcover
    unfold PlacementCovers at hcover
    have hcFinset : cell.1 ∈ placement.cells.toFinset := by
      simpa only [List.mem_toFinset] using hcover
    simp only [placementBenzelCells, Finset.mem_map, Finset.mem_attach]
    refine ⟨⟨cell.1, hcFinset⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem exact_cover_filter_singleton {m : ℕ} (tiling : LiteralTiling m)
    (cell : BenzelCell (m + 5)) :
    ∃ placement : LiteralPlacement m,
      tiling.1.filter (fun candidate => PlacementCovers candidate cell) =
        {placement} := by
  obtain ⟨placement, hp, hunique⟩ := tiling.2 cell
  refine ⟨placement, ?_⟩
  ext candidate
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hc
    exact hunique candidate hc
  · rintro rfl
    exact hp

theorem exact_cover_filter_card {m : ℕ} (tiling : LiteralTiling m)
    (cell : BenzelCell (m + 5)) :
    (tiling.1.filter (fun placement => PlacementCovers placement cell)).card = 1 := by
  obtain ⟨placement, hplacement⟩ := exact_cover_filter_singleton tiling cell
  rw [hplacement]
  simp

theorem tiling_incidence_double_count {m : ℕ} (tiling : LiteralTiling m) :
    ∑ placement ∈ tiling.1, (placementBenzelCells placement).card =
      ∑ cell : BenzelCell (m + 5),
        (tiling.1.filter fun placement => PlacementCovers placement cell).card := by
  classical
  calc
    ∑ placement ∈ tiling.1, (placementBenzelCells placement).card =
        ∑ placement ∈ tiling.1,
          ∑ cell : BenzelCell (m + 5),
            if PlacementCovers placement cell then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro placement _
      have hfilter :
          Finset.univ.filter (fun cell : BenzelCell (m + 5) =>
            PlacementCovers placement cell) = placementBenzelCells placement := by
        ext cell
        simp [mem_placementBenzelCells_iff]
      rw [← hfilter, Finset.card_filter]
    _ = ∑ cell : BenzelCell (m + 5),
        ∑ placement ∈ tiling.1,
          if PlacementCovers placement cell then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ cell : BenzelCell (m + 5),
        (tiling.1.filter fun placement => PlacementCovers placement cell).card := by
      apply Finset.sum_congr rfl
      intro cell _
      rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_filter]

theorem literal_tiling_card_mul_three {m : ℕ} (tiling : LiteralTiling m) :
    tiling.1.card * 3 = Fintype.card (BenzelCell (m + 5)) := by
  classical
  have hdouble := tiling_incidence_double_count tiling
  simp_rw [card_placementBenzelCells] at hdouble
  simp_rw [exact_cover_filter_card] at hdouble
  simpa [Finset.sum_const, nsmul_eq_mul] using hdouble

theorem two_dvd_tile_product (m : ℕ) :
    2 ∣ (m + 3) * (m + 6) := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · refine ⟨(2 * k + 3) * (k + 3), ?_⟩
    ring
  · refine ⟨(k + 2) * (2 * k + 7), ?_⟩
    ring

theorem literal_tiling_card {m : ℕ} (tiling : LiteralTiling m) :
    tiling.1.card = (m + 3) * (m + 6) / 2 := by
  have hincidence := literal_tiling_card_mul_three tiling
  have harea : Fintype.card (BenzelCell (m + 5)) =
      3 * (m + 3) * (m + 6) / 2 := by
    simpa using card_benzelCell (n := m + 5) (by omega)
  rw [harea] at hincidence
  have heven := two_dvd_tile_product m
  have hevenThree : 2 ∣ 3 * ((m + 3) * (m + 6)) :=
    dvd_mul_of_dvd_right heven 3
  have hevenArea : 2 ∣ 3 * (m + 3) * (m + 6) := by
    simpa [mul_assoc] using hevenThree
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_div heven (by norm_num : (2 : ℚ) ≠ 0)]
  have hincidenceQ :
      (tiling.1.card : ℚ) * 3 =
        ((3 * (m + 3) * (m + 6) / 2 : ℕ) : ℚ) := by
    exact_mod_cast hincidence
  rw [Nat.cast_div hevenArea (by norm_num : (2 : ℚ) ≠ 0)] at hincidenceQ
  push_cast at hincidenceQ ⊢
  nlinarith

end BenzelProblem6Kernel
