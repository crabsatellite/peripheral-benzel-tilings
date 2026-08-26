import FiniteDefects.D4PhaseEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact-cover energy double count on the d=4 diagonal -/

namespace FiniteDefects

open scoped BigOperators

def d4PlacementCellEmbedding {m : ℕ}
    (placement : D4LiteralPlacement m) :
    {cell : Cell // cell ∈ placement.cells.toFinset} ↪ D4Cell m where
  toFun cell :=
    ⟨cell.1, placement.2 cell.1 (by
      have hcList : cell.1 ∈ placement.cells := by
        simpa only [List.mem_toFinset] using cell.2
      simpa [D4LiteralPlacement.cells] using hcList)⟩
  inj' := by
    intro left right h
    apply Subtype.ext
    exact congrArg (fun cell : D4Cell m => cell.1) h

def d4PlacementCells {m : ℕ} (placement : D4LiteralPlacement m) :
    Finset (D4Cell m) :=
  placement.cells.toFinset.attach.map (d4PlacementCellEmbedding placement)

theorem card_d4PlacementCells {m : ℕ}
    (placement : D4LiteralPlacement m) :
    (d4PlacementCells placement).card = 3 := by
  rw [d4PlacementCells, Finset.card_map, Finset.card_attach]
  change (d4PlacementCellList placement.1).toFinset.card = 3
  rw [List.toFinset_card_of_nodup (d4PlacementCellList_nodup placement.1)]
  exact d4PlacementCellList_length placement.1

theorem mem_d4PlacementCells_iff {m : ℕ}
    (placement : D4LiteralPlacement m) (cell : D4Cell m) :
    cell ∈ d4PlacementCells placement ↔ D4PlacementCovers placement cell := by
  constructor
  · intro hmem
    simp only [d4PlacementCells, Finset.mem_map, Finset.mem_attach] at hmem
    obtain ⟨attached, _, heq⟩ := hmem
    have hval := congrArg Subtype.val heq
    have hcList : attached.1 ∈ placement.cells := by
      simpa only [List.mem_toFinset] using attached.2
    unfold D4PlacementCovers
    simpa [← hval] using hcList
  · intro hcover
    unfold D4PlacementCovers at hcover
    have hcFinset : cell.1 ∈ placement.cells.toFinset := by
      simpa only [List.mem_toFinset] using hcover
    simp only [d4PlacementCells, Finset.mem_map, Finset.mem_attach]
    refine ⟨⟨cell.1, hcFinset⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem d4_exact_cover_filter_singleton {m : ℕ}
    (tiling : D4LiteralTiling m) (cell : D4Cell m) :
    ∃ placement : D4LiteralPlacement m,
      tiling.1.filter (fun candidate => D4PlacementCovers candidate cell) =
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

theorem d4_placement_cell_energy_sum {m : ℕ}
    (placement : D4LiteralPlacement m) :
    ∑ cell ∈ d4PlacementCells placement, d4LiteralCellEnergy cell =
      d4LiteralPlacementEnergy placement := by
  classical
  calc
    (∑ cell ∈ d4PlacementCells placement,
        d4LiteralCellEnergy cell) =
        ∑ attached ∈ placement.cells.toFinset.attach,
          d4LiteralCellEnergy
            (d4PlacementCellEmbedding placement attached) := by
      rw [d4PlacementCells, Finset.sum_map]
    _ = ∑ rawCell ∈ placement.cells.toFinset,
          phaseCellEnergy (m + 2) rawCell := by
      conv_rhs => rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro attached _
      rw [d4LiteralCellEnergy_eq_phaseCellEnergy]
      rfl
    _ = (placement.cells.map (phaseCellEnergy (m + 2))).sum := by
      exact List.sum_toFinset (phaseCellEnergy (m + 2))
        (d4PlacementCellList_nodup placement.1)
    _ = d4LiteralPlacementEnergy placement :=
      phase_energy_sum_of_d4_placement placement

theorem d4_tiling_energy_double_count {m : ℕ}
    (tiling : D4LiteralTiling m) :
    ∑ placement ∈ tiling.1, d4LiteralPlacementEnergy placement =
      ∑ cell : D4Cell m, d4LiteralCellEnergy cell := by
  classical
  calc
    (∑ placement ∈ tiling.1, d4LiteralPlacementEnergy placement) =
        ∑ placement ∈ tiling.1,
          ∑ cell ∈ d4PlacementCells placement,
            d4LiteralCellEnergy cell := by
      apply Finset.sum_congr rfl
      intro placement _
      exact (d4_placement_cell_energy_sum placement).symm
    _ = ∑ placement ∈ tiling.1,
          ∑ cell : D4Cell m,
            if D4PlacementCovers placement cell then
              d4LiteralCellEnergy cell else 0 := by
      apply Finset.sum_congr rfl
      intro placement _
      have hfilter :
          Finset.univ.filter (fun cell : D4Cell m =>
            D4PlacementCovers placement cell) = d4PlacementCells placement := by
        ext cell
        simp [mem_d4PlacementCells_iff]
      rw [← hfilter, Finset.sum_filter]
    _ = ∑ cell : D4Cell m,
          ∑ placement ∈ tiling.1,
            if D4PlacementCovers placement cell then
              d4LiteralCellEnergy cell else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ cell : D4Cell m, d4LiteralCellEnergy cell := by
      apply Finset.sum_congr rfl
      intro cell _
      rw [← Finset.sum_filter]
      obtain ⟨placement, hplacement⟩ :=
        d4_exact_cover_filter_singleton tiling cell
      rw [hplacement]
      simp

theorem total_d4_literal_tile_energy {m : ℕ}
    (tiling : D4LiteralTiling m) :
    ∑ placement ∈ tiling.1, d4LiteralPlacementEnergy placement =
      3 * (m + 2 : ℤ) := by
  rw [d4_tiling_energy_double_count]
  exact total_d4_literal_cell_energy m

def d4BoneCount {m : ℕ} (tiling : D4LiteralTiling m) : ℕ :=
  (tiling.1.filter fun placement => placement.tile ≠ .stone).card

def IsD4WrongPhaseStone {m : ℕ}
    (placement : D4LiteralPlacement m) : Prop :=
  placement.tile = .stone ∧
    placementBaseResidue (m + 2) placement.base ≠ .r0

noncomputable instance isD4WrongPhaseStoneDecidable {m : ℕ}
    (placement : D4LiteralPlacement m) :
    Decidable (IsD4WrongPhaseStone placement) := Classical.propDecidable _

def IsD4ThreeOwnerBone {m : ℕ}
    (placement : D4LiteralPlacement m) : Prop :=
  match placement.tile, placementBaseResidue (m + 2) placement.base with
  | .boneA, .r1 => True
  | .boneB, .r2 => True
  | .boneC, .r1 => True
  | _, _ => False

noncomputable instance isD4ThreeOwnerBoneDecidable {m : ℕ}
    (placement : D4LiteralPlacement m) :
    Decidable (IsD4ThreeOwnerBone placement) := Classical.propDecidable _

noncomputable def d4WrongPhaseStoneCount {m : ℕ}
    (tiling : D4LiteralTiling m) : ℕ :=
  (tiling.1.filter IsD4WrongPhaseStone).card

noncomputable def d4ThreeOwnerBoneCount {m : ℕ}
    (tiling : D4LiteralTiling m) : ℕ :=
  (tiling.1.filter IsD4ThreeOwnerBone).card

theorem d4_literal_placement_energy_classification {m : ℕ}
    (placement : D4LiteralPlacement m) :
    d4LiteralPlacementEnergy placement =
      (if placement.tile ≠ .stone then (1 : ℤ) else 0) +
        3 * ((if IsD4WrongPhaseStone placement then (1 : ℤ) else 0) +
          if IsD4ThreeOwnerBone placement then (1 : ℤ) else 0) := by
  rcases htile : placement.tile with _ | _ | _ | _
  all_goals
    rcases hrho : placementBaseResidue (m + 2) placement.base with _ | _ | _
  all_goals
    simp [d4LiteralPlacementEnergy, htile, hrho, IsD4WrongPhaseStone,
      IsD4ThreeOwnerBone, stone_energy_by_residue, boneA_energy_by_residue,
      boneB_energy_by_residue, boneC_energy_by_residue]

theorem sum_int_indicator_eq_filter_card {α : Type*}
    [DecidableEq α] (s : Finset α) (predicate : α → Prop)
    [DecidablePred predicate] :
    ∑ x ∈ s, (if predicate x then (1 : ℤ) else 0) =
      ((s.filter predicate).card : ℤ) := by
  exact Finset.sum_boole (α := ℤ) predicate s

theorem d4_literal_tile_energy_count_formula {m : ℕ}
    (tiling : D4LiteralTiling m) :
    ∑ placement ∈ tiling.1, d4LiteralPlacementEnergy placement =
      (d4BoneCount tiling : ℤ) +
        3 * ((d4WrongPhaseStoneCount tiling : ℤ) +
          (d4ThreeOwnerBoneCount tiling : ℤ)) := by
  classical
  calc
    (∑ placement ∈ tiling.1, d4LiteralPlacementEnergy placement) =
        ∑ placement ∈ tiling.1,
          ((if placement.tile ≠ .stone then (1 : ℤ) else 0) +
            3 * ((if IsD4WrongPhaseStone placement then (1 : ℤ) else 0) +
              if IsD4ThreeOwnerBone placement then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro placement _
      exact d4_literal_placement_energy_classification placement
    _ = (∑ placement ∈ tiling.1,
          if placement.tile ≠ .stone then (1 : ℤ) else 0) +
        3 * ((∑ placement ∈ tiling.1,
            if IsD4WrongPhaseStone placement then (1 : ℤ) else 0) +
          ∑ placement ∈ tiling.1,
            if IsD4ThreeOwnerBone placement then (1 : ℤ) else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib]
    _ = (d4BoneCount tiling : ℤ) +
        3 * ((d4WrongPhaseStoneCount tiling : ℤ) +
          (d4ThreeOwnerBoneCount tiling : ℤ)) := by
      rw [sum_int_indicator_eq_filter_card,
        sum_int_indicator_eq_filter_card,
        sum_int_indicator_eq_filter_card]
      rfl

theorem d4_exact_energy_count_identity {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4BoneCount tiling : ℤ) +
        3 * ((d4WrongPhaseStoneCount tiling : ℤ) +
          (d4ThreeOwnerBoneCount tiling : ℤ)) =
      3 * (m + 2 : ℤ) := by
  rw [← d4_literal_tile_energy_count_formula tiling]
  exact total_d4_literal_tile_energy tiling

end FiniteDefects
