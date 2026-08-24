import BenzelProblem6Kernel.LiteralDegreeBounds

/-!
# In-phase stones and their unique simplex owners
-/

namespace BenzelProblem6Kernel

def stonePlacementFinset {m : ℕ} (tiling : LiteralTiling m) :
    Finset (LiteralPlacement m) :=
  tiling.1.filter fun placement => placement.tile = .stone

theorem stonePlacementFinset_card {m : ℕ} (tiling : LiteralTiling m) :
    (stonePlacementFinset tiling).card = rightStoneCount tiling := rfl

theorem stone_base_phase
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling}) :
    IsOwnerPhase (m + 3) placement.1.base := by
  have hp := placement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hp
  have hrho := every_literal_stone_in_phase hstone tiling placement.1 hp.1 hp.2
  have hbase := placementBaseResidue_spec (m + 3) placement.1.base
  unfold BaseHasResidue at hbase
  rw [hrho] at hbase
  simpa [Res3.value] using hbase

theorem stone_base_cell_mem
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling}) :
    inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor placement.1.base .zero) := by
  have hp := placement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hp
  have hinside := placement.1.2
  have hc00 : c00 ∈ protoCells placement.1.tile := by
    rw [hp.2]
    simp [protoCells]
  have hcell := hinside (translateLocalCell placement.1.base c00) (by
    simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
    exact ⟨c00, hc00, rfl⟩)
  simpa [cellForOwnerAnchor, translateLocalCell, c00] using hcell

theorem exists_stone_owner
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling}) :
    ∃ p : SimplexPoint (m + 3),
      ownerQ p = placement.1.base.1 ∧ ownerR p = placement.1.base.2 := by
  simpa [show m + 5 - 2 = m + 3 by omega] using
    phase_anchor_has_simplex (n := m + 5) (by omega)
      placement.1.base .zero
      (stone_base_phase hstone tiling placement)
      (stone_base_cell_mem tiling placement)

noncomputable def stoneOwner
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling}) :
    SimplexPoint (m + 3) :=
  (exists_stone_owner hstone tiling placement).choose

theorem stoneOwner_anchor
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling}) :
    ownerQ (stoneOwner hstone tiling placement) = placement.1.base.1 ∧
    ownerR (stoneOwner hstone tiling placement) = placement.1.base.2 :=
  (exists_stone_owner hstone tiling placement).choose_spec

theorem stone_placement_covers_owner_zero
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling}) :
    let owner := stoneOwner hstone tiling placement
    let cell : BenzelCell (m + 5) :=
      ⟨ownerCell owner .zero, by
        rw [ownerCell_eq_cellForOwnerAnchor,
          (stoneOwner_anchor hstone tiling placement).1,
          (stoneOwner_anchor hstone tiling placement).2]
        exact stone_base_cell_mem tiling placement⟩
    PlacementCovers placement.1 cell := by
  dsimp
  have hp := placement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hp
  have htile : placement.1.1.1 = .stone := hp.2
  change ownerCell (stoneOwner hstone tiling placement) .zero ∈ placement.1.cells
  rw [ownerCell_eq_cellForOwnerAnchor,
    (stoneOwner_anchor hstone tiling placement).1,
    (stoneOwner_anchor hstone tiling placement).2]
  simp only [cellForOwnerAnchor, LiteralPlacement.cells, placementCellList,
    List.mem_map]
  refine ⟨c00, ?_, ?_⟩
  · rw [htile]
    simp [protoCells]
  · simp [LiteralPlacement.base, translateLocalCell, c00]

def stoneLabelLocalCell : MicroLabel → LocalCell
  | .zero => c00
  | .one => c10
  | .two => c01

theorem stoneLabelLocalCell_mem (label : MicroLabel) :
    stoneLabelLocalCell label ∈ protoCells .stone := by
  rcases label <;> decide

theorem stoneLabelLocalCell_anchor (base : Cell) (label : MicroLabel) :
    cellForOwnerAnchor base label =
      translateLocalCell base (stoneLabelLocalCell label) := by
  rcases label <;>
    simp [stoneLabelLocalCell, cellForOwnerAnchor, translateLocalCell,
      c00, c10, c01]

theorem stone_placement_covers_owner_label
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling})
    (label : MicroLabel) :
    let owner := stoneOwner hstone tiling placement
    let cell : BenzelCell (m + 5) :=
      ⟨ownerCell owner label, by
        rw [ownerCell_eq_cellForOwnerAnchor,
          (stoneOwner_anchor hstone tiling placement).1,
          (stoneOwner_anchor hstone tiling placement).2,
          stoneLabelLocalCell_anchor]
        apply placement.1.2
        simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
        have hp := placement.2
        simp only [stonePlacementFinset, Finset.mem_filter] at hp
        refine ⟨stoneLabelLocalCell label, ?_, rfl⟩
        change stoneLabelLocalCell label ∈ protoCells placement.1.tile
        rw [hp.2]
        exact stoneLabelLocalCell_mem label⟩
    PlacementCovers placement.1 cell := by
  dsimp
  have hp := placement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hp
  change ownerCell (stoneOwner hstone tiling placement) label ∈ placement.1.cells
  rw [ownerCell_eq_cellForOwnerAnchor,
    (stoneOwner_anchor hstone tiling placement).1,
    (stoneOwner_anchor hstone tiling placement).2,
    stoneLabelLocalCell_anchor]
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
  refine ⟨stoneLabelLocalCell label, ?_, rfl⟩
  change stoneLabelLocalCell label ∈ protoCells placement.1.tile
  rw [hp.2]
  exact stoneLabelLocalCell_mem label

theorem stoneOwner_injective
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    Function.Injective (stoneOwner hstone tiling) := by
  intro left right howner
  have hleftMem := left.2
  have hrightMem := right.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hleftMem hrightMem
  let cell : BenzelCell (m + 5) :=
    ⟨ownerCell (stoneOwner hstone tiling left) .zero, by
      rw [ownerCell_eq_cellForOwnerAnchor,
        (stoneOwner_anchor hstone tiling left).1,
        (stoneOwner_anchor hstone tiling left).2]
      exact stone_base_cell_mem tiling left⟩
  have hleftCover : PlacementCovers left.1 cell := by
    exact stone_placement_covers_owner_zero hstone tiling left
  have hrightCover : PlacementCovers right.1 cell := by
    have hc := stone_placement_covers_owner_zero hstone tiling right
    have hcell :
        (⟨ownerCell (stoneOwner hstone tiling right) .zero, by
          rw [ownerCell_eq_cellForOwnerAnchor,
            (stoneOwner_anchor hstone tiling right).1,
            (stoneOwner_anchor hstone tiling right).2]
          exact stone_base_cell_mem tiling right⟩ : BenzelCell (m + 5)) = cell := by
      apply Subtype.ext
      simp [cell, howner]
    simpa [hcell] using hc
  obtain ⟨placement, _, hunique⟩ := tiling.2 cell
  have hl := hunique left.1 ⟨hleftMem.1, hleftCover⟩
  have hr := hunique right.1 ⟨hrightMem.1, hrightCover⟩
  apply Subtype.ext
  exact hl.trans hr.symm

noncomputable def stoneOwnerEmbedding
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    {p // p ∈ stonePlacementFinset tiling} ↪ SimplexPoint (m + 3) where
  toFun := stoneOwner hstone tiling
  inj' := stoneOwner_injective hstone tiling

noncomputable def stoneOwnerFinset
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : Finset (SimplexPoint (m + 3)) :=
  (stonePlacementFinset tiling).attach.map (stoneOwnerEmbedding hstone tiling)

theorem stoneOwnerFinset_card
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    (stoneOwnerFinset hstone tiling).card = m * (m + 3) / 2 := by
  rw [stoneOwnerFinset, Finset.card_map, Finset.card_attach,
    stonePlacementFinset_card, hstone m tiling]

theorem stoneOwner_local_cell_eq
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling})
    (localCell : LocalCell) (hlocal : localCell ∈ protoCells .stone) :
    ownerCell (stoneOwner hstone tiling placement) (localLabel .r0 localCell) =
      translateLocalCell placement.1.base localCell := by
  rw [ownerCell_eq_cellForOwnerAnchor,
    (stoneOwner_anchor hstone tiling placement).1,
    (stoneOwner_anchor hstone tiling placement).2]
  simp [protoCells] at hlocal
  rcases hlocal with rfl | rfl | rfl
  all_goals
    simp [localLabel, Res3.add, Res3.toLabel, cellForOwnerAnchor,
      translateLocalCell, c00, c10, c01]

theorem stone_covering_owner_eq
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (p : SimplexPoint (m + 3)) (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5) (ownerCell p label))
    (placement : {q // q ∈ stonePlacementFinset tiling})
    (hcover : PlacementCovers placement.1
      (⟨ownerCell p label, hmem⟩ : BenzelCell (m + 5))) :
    stoneOwner hstone tiling placement = p := by
  have hcoverRaw : ownerCell p label ∈ placement.1.cells := hcover
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map] at hcoverRaw
  obtain ⟨localCell, hlocalPlacement, hlocalEq⟩ := hcoverRaw
  have hp := placement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hp
  have hlocalStone : localCell ∈ protoCells .stone := by
    change localCell ∈ protoCells placement.1.tile at hlocalPlacement
    rw [hp.2] at hlocalPlacement
    exact hlocalPlacement
  have hstoneCell := stoneOwner_local_cell_eq hstone tiling placement
    localCell hlocalStone
  have hsame :
      ownerCell (stoneOwner hstone tiling placement) (localLabel .r0 localCell) =
        ownerCell p label := hstoneCell.trans hlocalEq
  exact (owner_representation_unique (n := m + 5)
    (ownerCell p label) (stoneOwner hstone tiling placement) p
    (localLabel .r0 localCell) label hsame rfl).1

end BenzelProblem6Kernel
