import FiniteDefects.D4EdgeRoles

/-! # Exact-cover placement roles at every owner label -/

namespace FiniteDefects

noncomputable def d4CoveringPlacement {m : ℕ}
    (tiling : D4LiteralTiling m) (cell : D4Cell m) :
    D4LiteralPlacement m :=
  (tiling.2 cell).choose

theorem d4CoveringPlacement_mem {m : ℕ}
    (tiling : D4LiteralTiling m) (cell : D4Cell m) :
    d4CoveringPlacement tiling cell ∈ tiling.1 :=
  (tiling.2 cell).choose_spec.1.1

theorem d4CoveringPlacement_covers {m : ℕ}
    (tiling : D4LiteralTiling m) (cell : D4Cell m) :
    D4PlacementCovers (d4CoveringPlacement tiling cell) cell :=
  (tiling.2 cell).choose_spec.1.2

theorem d4CoveringPlacement_unique {m : ℕ}
    (tiling : D4LiteralTiling m) (cell : D4Cell m)
    (placement : D4LiteralPlacement m)
    (hmem : placement ∈ tiling.1)
    (hcover : D4PlacementCovers placement cell) :
    placement = d4CoveringPlacement tiling cell :=
  (tiling.2 cell).choose_spec.2 placement ⟨hmem, hcover⟩

theorem exists_d4LocalCell_of_cover {m : ℕ}
    (placement : D4LiteralPlacement m) (cell : D4Cell m)
    (hcover : D4PlacementCovers placement cell) :
    ∃ localCell : D4PlacementLocalCell placement,
      d4RawCellOfLocal placement localCell = cell.1 := by
  unfold D4PlacementCovers D4LiteralPlacement.cells d4PlacementCellList at hcover
  simp only [List.mem_map] at hcover
  obtain ⟨localCell, hmem, heq⟩ := hcover
  exact ⟨⟨localCell, hmem⟩, heq⟩

theorem d4OwnerPairOfLocal_eq_of_rawCell {m : ℕ}
    (placement : D4LiteralPlacement m)
    (localCell : D4PlacementLocalCell placement)
    (p : SimplexPoint (m + 2)) (label : MicroLabel)
    (hraw : d4RawCellOfLocal placement localCell = ownerCell p label) :
    (d4OwnerPairOfLocal placement localCell).1.1 = p ∧
      (d4OwnerPairOfLocal placement localCell).1.2 = label := by
  have hcell := d4OwnerPairOfLocal_cell placement localCell
  exact owner_representation_unique (ownerCell p label)
    (d4OwnerPairOfLocal placement localCell).1.1 p
    (d4OwnerPairOfLocal placement localCell).1.2 label
    (hcell.trans hraw) rfl

theorem d4_bad_cover_is_core {m : ℕ} (tiling : D4LiteralTiling m)
    (p : SimplexPoint (m + 2)) (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label))
    (hcover : D4PlacementCovers (d4BadPlacement tiling)
      ⟨ownerCell p label, hpresent⟩) :
    p = d4DefectCore tiling label := by
  obtain ⟨localCell, hraw⟩ := exists_d4LocalCell_of_cover
    (d4BadPlacement tiling) ⟨ownerCell p label, hpresent⟩ hcover
  have hpair := d4OwnerPairOfLocal_eq_of_rawCell
    (d4BadPlacement tiling) localCell p label hraw
  have hcore := d4_bad_placement_local_is_core tiling localCell
  rw [hpair.2] at hcore
  exact hpair.1.symm.trans hcore

theorem d4_good_edge_cover_role {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (p : SimplexPoint (m + 2)) (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label))
    (hcover : D4PlacementCovers edge.placement
      ⟨ownerCell p label, hpresent⟩) :
    (p = edge.source ∧ label ≠ edge.boneClass.label) ∨
      (p = edge.target ∧ label = edge.boneClass.label) := by
  obtain ⟨localCell, hraw⟩ := exists_d4LocalCell_of_cover
    edge.placement ⟨ownerCell p label, hpresent⟩ hcover
  have hpair := d4OwnerPairOfLocal_eq_of_rawCell
    edge.placement localCell p label hraw
  rcases d4GoodEdge_local_role edge localCell with hsource | htarget
  · exact Or.inl ⟨hpair.1.symm.trans hsource.1,
      fun heq => hsource.2 (hpair.2.trans heq)⟩
  · exact Or.inr ⟨hpair.1.symm.trans htarget.1,
      hpair.2.symm.trans htarget.2⟩

def d4StoneLocalForLabel : MicroLabel → LocalCell
  | .zero => c00
  | .one => c10
  | .two => c01

theorem d4StoneLocalForLabel_mem (label : MicroLabel) :
    d4StoneLocalForLabel label ∈ protoCells .stone := by
  rcases label <;> decide

theorem d4StoneLocalForLabel_label (label : MicroLabel) :
    localLabel .r0 (d4StoneLocalForLabel label) = label := by
  rcases label <;> decide

theorem d4StoneLocalForLabel_shift (label : MicroLabel) :
    FiniteDefects.ownerShift .r0 (d4StoneLocalForLabel label) = (0, 0) := by
  rcases label <;> decide

def d4StoneLocal {m : ℕ} (placement : D4LiteralPlacement m)
    (htile : placement.tile = .stone) (label : MicroLabel) :
    D4PlacementLocalCell placement :=
  ⟨d4StoneLocalForLabel label, by
    rw [htile]
    exact d4StoneLocalForLabel_mem label⟩

noncomputable def d4StoneOwner {m : ℕ}
    (placement : D4LiteralPlacement m) (htile : placement.tile = .stone) :
    SimplexPoint (m + 2) :=
  (d4OwnerPairOfLocal placement (d4StoneLocal placement htile .zero)).1.1

theorem d4StoneLocal_pair {m : ℕ} (placement : D4LiteralPlacement m)
    (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0)
    (label : MicroLabel) :
    (d4OwnerPairOfLocal placement (d4StoneLocal placement htile label)).1.1 =
        d4StoneOwner placement htile ∧
      (d4OwnerPairOfLocal placement (d4StoneLocal placement htile label)).1.2 =
        label := by
  constructor
  · apply simplex_eq_of_owner_anchor
    · have hlabelAnchor := d4OwnerPairOfLocal_anchor placement
        (d4StoneLocal placement htile label)
      have hzeroAnchor := d4OwnerPairOfLocal_anchor placement
        (d4StoneLocal placement htile .zero)
      have hlabelShift : FiniteDefects.ownerShift
          (placementBaseResidue (m + 2) placement.base)
            (d4StoneLocal placement htile label).1 = (0, 0) := by
        rw [hphase]
        exact d4StoneLocalForLabel_shift label
      have hzeroShift : FiniteDefects.ownerShift
          (placementBaseResidue (m + 2) placement.base)
            (d4StoneLocal placement htile .zero).1 = (0, 0) := by
        rw [hphase]
        exact d4StoneLocalForLabel_shift .zero
      have hlabelQ := congrArg Prod.fst hlabelAnchor
      have hzeroQ := congrArg Prod.fst hzeroAnchor
      rw [hlabelShift] at hlabelQ
      rw [hzeroShift] at hzeroQ
      exact hlabelQ.trans hzeroQ.symm
    · have hlabelAnchor := d4OwnerPairOfLocal_anchor placement
        (d4StoneLocal placement htile label)
      have hzeroAnchor := d4OwnerPairOfLocal_anchor placement
        (d4StoneLocal placement htile .zero)
      have hlabelShift : FiniteDefects.ownerShift
          (placementBaseResidue (m + 2) placement.base)
            (d4StoneLocal placement htile label).1 = (0, 0) := by
        rw [hphase]
        exact d4StoneLocalForLabel_shift label
      have hzeroShift : FiniteDefects.ownerShift
          (placementBaseResidue (m + 2) placement.base)
            (d4StoneLocal placement htile .zero).1 = (0, 0) := by
        rw [hphase]
        exact d4StoneLocalForLabel_shift .zero
      have hlabelR := congrArg Prod.snd hlabelAnchor
      have hzeroR := congrArg Prod.snd hzeroAnchor
      rw [hlabelShift] at hlabelR
      rw [hzeroShift] at hzeroR
      exact hlabelR.trans hzeroR.symm
  · rw [d4OwnerPairOfLocal_label, hphase]
    exact d4StoneLocalForLabel_label label

theorem d4Stone_rawCellForLabel {m : ℕ}
    (placement : D4LiteralPlacement m) (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0)
    (label : MicroLabel) :
    d4RawCellOfLocal placement (d4StoneLocal placement htile label) =
      ownerCell (d4StoneOwner placement htile) label := by
  have hcell := d4OwnerPairOfLocal_cell placement
    (d4StoneLocal placement htile label)
  have hpair := d4StoneLocal_pair placement htile hphase label
  rw [hpair.1, hpair.2] at hcell
  exact hcell.symm

theorem d4StoneOwner_full {m : ℕ}
    (placement : D4LiteralPlacement m) (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0) :
    ∀ label, inBenzel (m + 4) (2 * m + 4)
      (ownerCell (d4StoneOwner placement htile) label) := by
  intro label
  have hraw := d4Stone_rawCellForLabel placement htile hphase label
  rw [← hraw]
  exact (d4CellOfLocal placement (d4StoneLocal placement htile label)).2

theorem d4Stone_covers_owner_label {m : ℕ}
    (placement : D4LiteralPlacement m) (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0)
    (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell (d4StoneOwner placement htile) label)) :
    D4PlacementCovers placement
      ⟨ownerCell (d4StoneOwner placement htile) label, hpresent⟩ := by
  unfold D4PlacementCovers
  change ownerCell (d4StoneOwner placement htile) label ∈ placement.cells
  rw [← d4Stone_rawCellForLabel placement htile hphase label]
  simp only [D4LiteralPlacement.cells, d4PlacementCellList, List.mem_map]
  refine ⟨d4StoneLocalForLabel label, ?_, rfl⟩
  change d4StoneLocalForLabel label ∈ protoCells placement.tile
  rw [htile]
  exact d4StoneLocalForLabel_mem label

theorem d4InPhaseStone_local_owner {m : ℕ}
    (placement : D4LiteralPlacement m) (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0)
    (localCell : D4PlacementLocalCell placement) :
    (d4OwnerPairOfLocal placement localCell).1.1 =
      d4StoneOwner placement htile := by
  rcases localCell with ⟨localCell, hmem⟩
  have hmemStone : localCell ∈ protoCells .stone := by
    rw [← htile]
    exact hmem
  simp only [protoCells, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hmemStone
  rcases hmemStone with rfl | rfl | rfl
  all_goals
    apply simplex_eq_of_owner_anchor
  all_goals
    have hlocalAnchor := d4OwnerPairOfLocal_anchor placement ⟨_, hmem⟩
    have hzeroAnchor := d4OwnerPairOfLocal_anchor placement
      (d4StoneLocal placement htile .zero)
  all_goals
    rw [hphase] at hlocalAnchor hzeroAnchor
    simp [d4StoneLocal, d4StoneLocalForLabel, ownerShift, localLabel,
      Res3.add, Res3.toLabel, c00, c10, c01] at hlocalAnchor hzeroAnchor
  all_goals
    first
    | have hl := congrArg Prod.fst hlocalAnchor
      have hz := congrArg Prod.fst hzeroAnchor
      exact hl.trans hz.symm
    | have hl := congrArg Prod.snd hlocalAnchor
      have hz := congrArg Prod.snd hzeroAnchor
      exact hl.trans hz.symm

theorem d4_good_stone_cover_owner {m : ℕ}
    (placement : D4LiteralPlacement m)
    (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0)
    (p : SimplexPoint (m + 2)) (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label))
    (hcover : D4PlacementCovers placement ⟨ownerCell p label, hpresent⟩) :
    p = d4StoneOwner placement htile := by
  obtain ⟨localCell, hraw⟩ := exists_d4LocalCell_of_cover
    placement ⟨ownerCell p label, hpresent⟩ hcover
  have hpair := d4OwnerPairOfLocal_eq_of_rawCell
    placement localCell p label hraw
  exact hpair.1.symm.trans
    (d4InPhaseStone_local_owner placement htile hphase localCell)

end FiniteDefects
