import FiniteDefects.D4UniqueDefect

/-! # Literal owner and label of every placed prototile cell -/

namespace FiniteDefects

abbrev D4PlacementLocalCell {m : ℕ} (placement : D4LiteralPlacement m) :=
  {localCell : LocalCell // localCell ∈ protoCells placement.tile}

def d4RawCellOfLocal {m : ℕ} (placement : D4LiteralPlacement m)
    (localCell : D4PlacementLocalCell placement) : Cell :=
  translateLocalCell placement.base localCell.1

def d4CellOfLocal {m : ℕ} (placement : D4LiteralPlacement m)
    (localCell : D4PlacementLocalCell placement) : D4Cell m :=
  ⟨d4RawCellOfLocal placement localCell, placement.2 _ (by
    simp only [D4LiteralPlacement.cells, d4PlacementCellList,
      List.mem_map]
    exact ⟨localCell.1, localCell.2, rfl⟩)⟩

noncomputable def d4OwnerPairOfLocal {m : ℕ}
    (placement : D4LiteralPlacement m)
    (localCell : D4PlacementLocalCell placement) :
    PresentD4OwnerLabel m :=
  (d4OwnerCellEquiv m).symm (d4CellOfLocal placement localCell)

theorem d4OwnerPairOfLocal_cell {m : ℕ}
    (placement : D4LiteralPlacement m)
    (localCell : D4PlacementLocalCell placement) :
    ownerCell (d4OwnerPairOfLocal placement localCell).1.1
        (d4OwnerPairOfLocal placement localCell).1.2 =
      d4RawCellOfLocal placement localCell := by
  have h := (d4OwnerCellEquiv m).apply_symm_apply
    (d4CellOfLocal placement localCell)
  exact congrArg Subtype.val h

theorem d4OwnerPairOfLocal_label {m : ℕ}
    (placement : D4LiteralPlacement m)
    (localCell : D4PlacementLocalCell placement) :
    (d4OwnerPairOfLocal placement localCell).1.2 =
      localLabel (placementBaseResidue (m + 2) placement.base) localCell.1 := by
  let pair := d4OwnerPairOfLocal placement localCell
  let rho := placementBaseResidue (m + 2) placement.base
  have hpairAnchor :
      ownerAnchorForCell (d4RawCellOfLocal placement localCell) pair.1.2 =
        (ownerQ pair.1.1, ownerR pair.1.1) := by
    rw [← d4OwnerPairOfLocal_cell placement localCell,
      ownerCell_eq_cellForOwnerAnchor]
    exact anchor_cell_roundtrip (ownerQ pair.1.1, ownerR pair.1.1) pair.1.2
  have hpairPhase :
      IsOwnerPhase (m + 2)
        (ownerAnchorForCell (d4RawCellOfLocal placement localCell) pair.1.2) := by
    rw [hpairAnchor]
    exact owner_anchor_is_phase pair.1.1
  have hlocalPhase :
      IsOwnerPhase (m + 2)
        (ownerAnchorForCell (d4RawCellOfLocal placement localCell)
          (localLabel rho localCell.1)) := by
    rw [show ownerAnchorForCell (d4RawCellOfLocal placement localCell)
        (localLabel rho localCell.1) =
      (placement.base.1 + (ownerShift rho localCell.1).1,
        placement.base.2 + (ownerShift rho localCell.1).2) by
      exact ownerAnchorForCell_translate_eq placement.base rho localCell.1]
    exact translated_local_owner_is_phase (m + 2) placement.base
      placement.tile localCell.1 localCell.2
  obtain ⟨chosen, _, hunique⟩ :=
    unique_phase_owner_label (m + 2)
      (d4RawCellOfLocal placement localCell)
  exact (hunique pair.1.2 hpairPhase).trans
    (hunique (localLabel rho localCell.1) hlocalPhase).symm

theorem d4OwnerPairOfLocal_anchor {m : ℕ}
    (placement : D4LiteralPlacement m)
    (localCell : D4PlacementLocalCell placement) :
    (ownerQ (d4OwnerPairOfLocal placement localCell).1.1,
      ownerR (d4OwnerPairOfLocal placement localCell).1.1) =
      (placement.base.1 +
          (ownerShift (placementBaseResidue (m + 2) placement.base)
            localCell.1).1,
        placement.base.2 +
          (ownerShift (placementBaseResidue (m + 2) placement.base)
            localCell.1).2) := by
  let pair := d4OwnerPairOfLocal placement localCell
  let rho := placementBaseResidue (m + 2) placement.base
  have hpairAnchor :
      ownerAnchorForCell (d4RawCellOfLocal placement localCell) pair.1.2 =
        (ownerQ pair.1.1, ownerR pair.1.1) := by
    rw [← d4OwnerPairOfLocal_cell placement localCell,
      ownerCell_eq_cellForOwnerAnchor]
    exact anchor_cell_roundtrip (ownerQ pair.1.1, ownerR pair.1.1) pair.1.2
  have hlocalAnchor := ownerAnchorForCell_translate_eq
    placement.base rho localCell.1
  rw [d4OwnerPairOfLocal_label] at hpairAnchor
  exact hpairAnchor.symm.trans hlocalAnchor

theorem d4OwnerPairOfLocal_eq_of_datum {m : ℕ}
    (placement : D4LiteralPlacement m)
    (left right : D4PlacementLocalCell placement)
    (hdatum :
      localOwnerDatum (placementBaseResidue (m + 2) placement.base) left.1 =
      localOwnerDatum (placementBaseResidue (m + 2) placement.base) right.1) :
    d4OwnerPairOfLocal placement left = d4OwnerPairOfLocal placement right := by
  have hanchorLeft := d4OwnerPairOfLocal_anchor placement left
  have hanchorRight := d4OwnerPairOfLocal_anchor placement right
  have hshiftCell := congrArg (fun datum : Cell × MicroLabel => datum.1) hdatum
  have hshiftQ := congrArg Prod.fst hshiftCell
  have hshiftR := congrArg Prod.snd hshiftCell
  dsimp [localOwnerDatum] at hshiftQ hshiftR
  have hq : ownerQ (d4OwnerPairOfLocal placement left).1.1 =
      ownerQ (d4OwnerPairOfLocal placement right).1.1 := by
    have hleft := congrArg Prod.fst hanchorLeft
    have hright := congrArg Prod.fst hanchorRight
    omega
  have hr : ownerR (d4OwnerPairOfLocal placement left).1.1 =
      ownerR (d4OwnerPairOfLocal placement right).1.1 := by
    have hleft := congrArg Prod.snd hanchorLeft
    have hright := congrArg Prod.snd hanchorRight
    omega
  have hp : (d4OwnerPairOfLocal placement left).1.1 =
      (d4OwnerPairOfLocal placement right).1.1 := by
    apply simplexPoint_ext
    all_goals
      have hu := recover_u_numerator
        (d4OwnerPairOfLocal placement left).1.1
      have hu' := recover_u_numerator
        (d4OwnerPairOfLocal placement right).1.1
      have hv := recover_v_numerator
        (d4OwnerPairOfLocal placement left).1.1
      have hv' := recover_v_numerator
        (d4OwnerPairOfLocal placement right).1.1
      have hw := recover_w_numerator
        (d4OwnerPairOfLocal placement left).1.1
      have hw' := recover_w_numerator
        (d4OwnerPairOfLocal placement right).1.1
      omega
  have hlabel : (d4OwnerPairOfLocal placement left).1.2 =
      (d4OwnerPairOfLocal placement right).1.2 := by
    rw [d4OwnerPairOfLocal_label, d4OwnerPairOfLocal_label]
    exact congrArg Prod.snd hdatum
  apply Subtype.ext
  exact Prod.ext hp hlabel

theorem stone_r1_profile :
    boneOwnerProfile .stone .r1 =
      [((-1, 0), .one), ((1, -1), .two), ((0, 1), .zero)] := by
  decide

theorem stone_r2_profile :
    boneOwnerProfile .stone .r2 =
      [((0, -1), .two), ((1, 0), .zero), ((-1, 1), .one)] := by
  decide

theorem boneA_r1_profile :
    boneOwnerProfile .boneA .r1 =
      [((-1, 0), .one), ((1, -1), .two), ((2, 0), .zero)] := by
  decide

theorem boneB_r2_profile :
    boneOwnerProfile .boneB .r2 =
      [((0, -1), .two), ((-1, 1), .one), ((0, 2), .zero)] := by
  decide

theorem boneC_r1_profile :
    boneOwnerProfile .boneC .r1 =
      [((-1, 0), .one), ((1, -1), .zero), ((2, -3), .two)] := by
  decide

inductive D4DefectKind
  | stone1 | stone2 | boneA | boneB | boneC
  deriving DecidableEq, Repr

def D4DefectKind.tile : D4DefectKind → ProtoTile
  | .stone1 | .stone2 => .stone
  | .boneA => .boneA
  | .boneB => .boneB
  | .boneC => .boneC

def D4DefectKind.residue : D4DefectKind → Res3
  | .stone1 | .boneA | .boneC => .r1
  | .stone2 | .boneB => .r2

def D4IsDefectClass {m : ℕ} (placement : D4LiteralPlacement m)
    (kind : D4DefectKind) : Prop :=
  placement.tile = kind.tile ∧
    placementBaseResidue (m + 2) placement.base = kind.residue

theorem exists_unique_d4DefectKind {m : ℕ}
    (placement : D4LiteralPlacement m)
    (hbad : IsD4BadPlacement placement) :
    ∃! kind : D4DefectKind, D4IsDefectClass placement kind := by
  rcases htile : placement.tile with _ | _ | _ | _
  · rcases hrho : placementBaseResidue (m + 2) placement.base with _ | _ | _
    · simp [IsD4BadPlacement, IsD4WrongPhaseStone,
        IsD4ThreeOwnerBone, htile, hrho] at hbad
    · refine ⟨.stone1, by simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho], ?_⟩
      intro kind hk
      rcases kind <;> simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho] at hk ⊢
    · refine ⟨.stone2, by simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho], ?_⟩
      intro kind hk
      rcases kind <;> simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho] at hk ⊢
  · rcases hrho : placementBaseResidue (m + 2) placement.base with _ | _ | _
    · simp [IsD4BadPlacement, IsD4WrongPhaseStone,
        IsD4ThreeOwnerBone, htile, hrho] at hbad
    · refine ⟨.boneA, by simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho], ?_⟩
      intro kind hk
      rcases kind <;> simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho] at hk ⊢
    · simp [IsD4BadPlacement, IsD4WrongPhaseStone,
        IsD4ThreeOwnerBone, htile, hrho] at hbad
  · rcases hrho : placementBaseResidue (m + 2) placement.base with _ | _ | _
    · simp [IsD4BadPlacement, IsD4WrongPhaseStone,
        IsD4ThreeOwnerBone, htile, hrho] at hbad
    · simp [IsD4BadPlacement, IsD4WrongPhaseStone,
        IsD4ThreeOwnerBone, htile, hrho] at hbad
    · refine ⟨.boneB, by simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho], ?_⟩
      intro kind hk
      rcases kind <;> simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho] at hk ⊢
  · rcases hrho : placementBaseResidue (m + 2) placement.base with _ | _ | _
    · simp [IsD4BadPlacement, IsD4WrongPhaseStone,
        IsD4ThreeOwnerBone, htile, hrho] at hbad
    · refine ⟨.boneC, by simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho], ?_⟩
      intro kind hk
      rcases kind <;> simp [D4IsDefectClass, D4DefectKind.tile,
        D4DefectKind.residue, htile, hrho] at hk ⊢
    · simp [IsD4BadPlacement, IsD4WrongPhaseStone,
        IsD4ThreeOwnerBone, htile, hrho] at hbad

noncomputable def d4DefectKind {m : ℕ} (tiling : D4LiteralTiling m) :
    D4DefectKind :=
  (exists_unique_d4DefectKind (d4BadPlacement tiling)
    (d4BadPlacement_isBad tiling)).choose

theorem d4DefectKind_spec {m : ℕ} (tiling : D4LiteralTiling m) :
    D4IsDefectClass (d4BadPlacement tiling) (d4DefectKind tiling) :=
  (exists_unique_d4DefectKind (d4BadPlacement tiling)
    (d4BadPlacement_isBad tiling)).choose_spec.1

end FiniteDefects
