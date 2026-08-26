import D4KernelOnly.GeneralLiteralTiling
import FiniteDefects.D4PhaseEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact-cover energy double count for every offset -/

namespace FiniteDefects

open scoped BigOperators

noncomputable def offsetLiteralCellEnergy {t d : ℕ}
    (cell : OffsetCell t d) : ℤ := phaseCellEnergy t cell.1

def offsetLiteralPlacementEnergy {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) : ℤ :=
  literalTileEnergy placement.tile placement.base.1 placement.base.2
    (placementBaseResidue t placement.base)

theorem phase_energy_sum_of_offset_placement {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    (placement.cells.map (phaseCellEnergy t)).sum =
      offsetLiteralPlacementEnergy placement := by
  change
    (((protoCells placement.tile).map
      (translateLocalCell placement.base)).map
      (phaseCellEnergy t)).sum = _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro localCell hlocal
  exact phaseCellEnergy_translate t placement.base placement.tile localCell hlocal

def offsetPlacementCellEmbedding {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    {cell : Cell // cell ∈ placement.cells.toFinset} ↪ OffsetCell t d where
  toFun cell :=
    ⟨cell.1, placement.2 cell.1 (by
      have hcList : cell.1 ∈ placement.cells := by
        simpa only [List.mem_toFinset] using cell.2
      simpa [OffsetLiteralPlacement.cells] using hcList)⟩
  inj' := by
    intro left right h
    apply Subtype.ext
    exact congrArg (fun cell : OffsetCell t d => cell.1) h

def offsetPlacementCells {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) : Finset (OffsetCell t d) :=
  placement.cells.toFinset.attach.map (offsetPlacementCellEmbedding placement)

theorem card_offsetPlacementCells {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    (offsetPlacementCells placement).card = 3 := by
  rw [offsetPlacementCells, Finset.card_map, Finset.card_attach]
  change (offsetPlacementCellList placement.1).toFinset.card = 3
  rw [List.toFinset_card_of_nodup (offsetPlacementCellList_nodup placement.1)]
  exact offsetPlacementCellList_length placement.1

theorem mem_offsetPlacementCells_iff {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) (cell : OffsetCell t d) :
    cell ∈ offsetPlacementCells placement ↔
      OffsetPlacementCovers placement cell := by
  constructor
  · intro hmem
    simp only [offsetPlacementCells, Finset.mem_map, Finset.mem_attach] at hmem
    obtain ⟨attached, _, heq⟩ := hmem
    have hval := congrArg Subtype.val heq
    have hcList : attached.1 ∈ placement.cells := by
      simpa only [List.mem_toFinset] using attached.2
    unfold OffsetPlacementCovers
    simpa [← hval] using hcList
  · intro hcover
    unfold OffsetPlacementCovers at hcover
    have hcFinset : cell.1 ∈ placement.cells.toFinset := by
      simpa only [List.mem_toFinset] using hcover
    simp only [offsetPlacementCells, Finset.mem_map, Finset.mem_attach]
    refine ⟨⟨cell.1, hcFinset⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem offset_exact_cover_filter_singleton {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) (cell : OffsetCell t d) :
    ∃ placement : OffsetLiteralPlacement t d,
      tiling.1.filter (fun candidate => OffsetPlacementCovers candidate cell) =
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

theorem offset_placement_cell_energy_sum {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    ∑ cell ∈ offsetPlacementCells placement, offsetLiteralCellEnergy cell =
      offsetLiteralPlacementEnergy placement := by
  classical
  calc
    (∑ cell ∈ offsetPlacementCells placement,
        offsetLiteralCellEnergy cell) =
        ∑ attached ∈ placement.cells.toFinset.attach,
          offsetLiteralCellEnergy
            (offsetPlacementCellEmbedding placement attached) := by
      rw [offsetPlacementCells, Finset.sum_map]
    _ = ∑ rawCell ∈ placement.cells.toFinset, phaseCellEnergy t rawCell := by
      conv_rhs => rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro attached _
      rfl
    _ = (placement.cells.map (phaseCellEnergy t)).sum := by
      exact List.sum_toFinset (phaseCellEnergy t)
        (offsetPlacementCellList_nodup placement.1)
    _ = offsetLiteralPlacementEnergy placement :=
      phase_energy_sum_of_offset_placement placement

theorem offset_tiling_energy_double_count {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    ∑ placement ∈ tiling.1, offsetLiteralPlacementEnergy placement =
      ∑ cell : OffsetCell t d, offsetLiteralCellEnergy cell := by
  classical
  calc
    (∑ placement ∈ tiling.1, offsetLiteralPlacementEnergy placement) =
        ∑ placement ∈ tiling.1,
          ∑ cell ∈ offsetPlacementCells placement,
            offsetLiteralCellEnergy cell := by
      apply Finset.sum_congr rfl
      intro placement _
      exact (offset_placement_cell_energy_sum placement).symm
    _ = ∑ placement ∈ tiling.1,
          ∑ cell : OffsetCell t d,
            if OffsetPlacementCovers placement cell then
              offsetLiteralCellEnergy cell else 0 := by
      apply Finset.sum_congr rfl
      intro placement _
      have hfilter :
          Finset.univ.filter (fun cell : OffsetCell t d =>
            OffsetPlacementCovers placement cell) =
              offsetPlacementCells placement := by
        ext cell
        simp [mem_offsetPlacementCells_iff]
      rw [← hfilter, Finset.sum_filter]
    _ = ∑ cell : OffsetCell t d,
          ∑ placement ∈ tiling.1,
            if OffsetPlacementCovers placement cell then
              offsetLiteralCellEnergy cell else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ cell : OffsetCell t d, offsetLiteralCellEnergy cell := by
      apply Finset.sum_congr rfl
      intro cell _
      rw [← Finset.sum_filter]
      obtain ⟨placement, hplacement⟩ :=
        offset_exact_cover_filter_singleton tiling cell
      rw [hplacement]
      simp

def offsetBoneCount {t d : ℕ} (tiling : OffsetLiteralTiling t d) : ℕ :=
  (tiling.1.filter fun placement => placement.tile ≠ .stone).card

def IsOffsetWrongPhaseStone {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) : Prop :=
  placement.tile = .stone ∧ placementBaseResidue t placement.base ≠ .r0

noncomputable instance isOffsetWrongPhaseStoneDecidable {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    Decidable (IsOffsetWrongPhaseStone placement) := Classical.propDecidable _

def IsOffsetThreeOwnerBone {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) : Prop :=
  match placement.tile, placementBaseResidue t placement.base with
  | .boneA, .r1 => True
  | .boneB, .r2 => True
  | .boneC, .r1 => True
  | _, _ => False

noncomputable instance isOffsetThreeOwnerBoneDecidable {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    Decidable (IsOffsetThreeOwnerBone placement) := Classical.propDecidable _

noncomputable def offsetWrongPhaseStoneCount {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) : ℕ :=
  (tiling.1.filter IsOffsetWrongPhaseStone).card

noncomputable def offsetThreeOwnerBoneCount {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) : ℕ :=
  (tiling.1.filter IsOffsetThreeOwnerBone).card

theorem offset_literal_placement_energy_classification {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    offsetLiteralPlacementEnergy placement =
      (if placement.tile ≠ .stone then (1 : ℤ) else 0) +
        3 * ((if IsOffsetWrongPhaseStone placement then (1 : ℤ) else 0) +
          if IsOffsetThreeOwnerBone placement then (1 : ℤ) else 0) := by
  rcases htile : placement.tile with _ | _ | _ | _
  all_goals rcases hrho : placementBaseResidue t placement.base with _ | _ | _
  all_goals
    simp [offsetLiteralPlacementEnergy, htile, hrho,
      IsOffsetWrongPhaseStone, IsOffsetThreeOwnerBone,
      stone_energy_by_residue, boneA_energy_by_residue,
      boneB_energy_by_residue, boneC_energy_by_residue]

theorem offset_sum_int_indicator_eq_filter_card {α : Type*}
    [DecidableEq α] (s : Finset α) (predicate : α → Prop)
    [DecidablePred predicate] :
    ∑ x ∈ s, (if predicate x then (1 : ℤ) else 0) =
      ((s.filter predicate).card : ℤ) := by
  exact Finset.sum_boole (α := ℤ) predicate s

theorem offset_literal_tile_energy_count_formula {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    ∑ placement ∈ tiling.1, offsetLiteralPlacementEnergy placement =
      (offsetBoneCount tiling : ℤ) +
        3 * ((offsetWrongPhaseStoneCount tiling : ℤ) +
          (offsetThreeOwnerBoneCount tiling : ℤ)) := by
  classical
  calc
    (∑ placement ∈ tiling.1, offsetLiteralPlacementEnergy placement) =
        ∑ placement ∈ tiling.1,
          ((if placement.tile ≠ .stone then (1 : ℤ) else 0) +
            3 * ((if IsOffsetWrongPhaseStone placement then (1 : ℤ) else 0) +
              if IsOffsetThreeOwnerBone placement then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro placement _
      exact offset_literal_placement_energy_classification placement
    _ = (∑ placement ∈ tiling.1,
          if placement.tile ≠ .stone then (1 : ℤ) else 0) +
        3 * ((∑ placement ∈ tiling.1,
            if IsOffsetWrongPhaseStone placement then (1 : ℤ) else 0) +
          ∑ placement ∈ tiling.1,
            if IsOffsetThreeOwnerBone placement then (1 : ℤ) else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib]
    _ = (offsetBoneCount tiling : ℤ) +
        3 * ((offsetWrongPhaseStoneCount tiling : ℤ) +
          (offsetThreeOwnerBoneCount tiling : ℤ)) := by
      rw [offset_sum_int_indicator_eq_filter_card,
        offset_sum_int_indicator_eq_filter_card,
        offset_sum_int_indicator_eq_filter_card]
      rfl

end FiniteDefects
