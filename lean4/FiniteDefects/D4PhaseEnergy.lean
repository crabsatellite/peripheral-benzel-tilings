import FiniteDefects.D4RegionEnergy

/-! # Literal placement energy from the unique phase owner -/

namespace FiniteDefects

theorem shifted_anchor_is_phase {t : ℕ} {q r k dq dr : ℤ}
    (hbase : q - r ≡ (t : ℤ) + k [ZMOD 3])
    (hdiv : (3 : ℤ) ∣ k + dq - dr) :
    IsOwnerPhase t (q + dq, r + dr) := by
  unfold IsOwnerPhase
  have hshift := hbase.add (Int.ModEq.refl (dq - dr))
  have hzero : k + dq - dr ≡ 0 [ZMOD 3] := hdiv.modEq_zero_int
  have htarget := (Int.ModEq.refl (t : ℤ)).add hzero
  have hmiddle : (t : ℤ) + k + (dq - dr) ≡ (t : ℤ) [ZMOD 3] := by
    convert htarget using 1; ring
  have hfinal := hshift.trans hmiddle
  convert hfinal using 1; ring

theorem translated_local_owner_is_phase (t : ℕ) (base : Cell)
    (tile : ProtoTile) (localCell : LocalCell)
    (hlocal : localCell ∈ protoCells tile) :
    IsOwnerPhase t
      (base.1 + (ownerShift (placementBaseResidue t base) localCell).1,
        base.2 + (ownerShift (placementBaseResidue t base) localCell).2) := by
  have hbase := placementBaseResidue_spec t base
  unfold BaseHasResidue at hbase
  rcases hrho : placementBaseResidue t base with _ | _ | _
  all_goals simp only [hrho, Res3.value] at hbase
  all_goals
    rcases tile with _ | _ | _ | _ <;>
      simp [protoCells] at hlocal
  all_goals
    rcases hlocal with rfl | rfl | rfl <;>
      simp only [ownerShift, localLabel, Res3.add, Res3.toLabel,
        c00, c10, c20, c01, c02, c1m1, c2m2]
  all_goals
    apply shifted_anchor_is_phase hbase; norm_num

noncomputable def phaseOwnerLabel (t : ℕ) (cell : Cell) : MicroLabel :=
  (unique_phase_owner_label t cell).choose

theorem phaseOwnerLabel_is_phase (t : ℕ) (cell : Cell) :
    IsOwnerPhase t (ownerAnchorForCell cell (phaseOwnerLabel t cell)) :=
  (unique_phase_owner_label t cell).choose_spec.1

theorem phaseOwnerLabel_unique (t : ℕ) (cell : Cell) (label : MicroLabel)
    (hlabel : IsOwnerPhase t (ownerAnchorForCell cell label)) :
    phaseOwnerLabel t cell = label :=
  ((unique_phase_owner_label t cell).choose_spec.2 label hlabel).symm

noncomputable def phaseCellEnergy (t : ℕ) (cell : Cell) : ℤ :=
  ownerPotential (phaseOwnerLabel t cell)
    (ownerAnchorForCell cell (phaseOwnerLabel t cell)).1
    (ownerAnchorForCell cell (phaseOwnerLabel t cell)).2

theorem ownerAnchorForCell_translate_eq (base : Cell) (rho : Res3)
    (localCell : LocalCell) :
    ownerAnchorForCell (translateLocalCell base localCell)
        (localLabel rho localCell) =
      (base.1 + (ownerShift rho localCell).1,
        base.2 + (ownerShift rho localCell).2) := by
  rcases hlabel : localLabel rho localCell with _ | _ | _ <;>
    simp [translateLocalCell, ownerShift, hlabel, ownerAnchorForCell]
  all_goals ring

theorem phaseCellEnergy_translate (t : ℕ) (base : Cell)
    (tile : ProtoTile) (localCell : LocalCell)
    (hlocal : localCell ∈ protoCells tile) :
    phaseCellEnergy t (translateLocalCell base localCell) =
      localCellEnergy base.1 base.2 (placementBaseResidue t base) localCell := by
  let rho := placementBaseResidue t base
  have hanchor := ownerAnchorForCell_translate_eq base rho localCell
  have hphase :
      IsOwnerPhase t
        (ownerAnchorForCell (translateLocalCell base localCell)
          (localLabel rho localCell)) := by
    rw [hanchor]
    exact translated_local_owner_is_phase t base tile localCell hlocal
  have hlabel := phaseOwnerLabel_unique t (translateLocalCell base localCell)
    (localLabel rho localCell) hphase
  simp only [phaseCellEnergy, localCellEnergy]
  rw [hlabel, hanchor]

theorem d4LiteralCellEnergy_eq_phaseCellEnergy {m : ℕ}
    (cell : D4Cell m) :
    d4LiteralCellEnergy cell = phaseCellEnergy (m + 2) cell.1 := by
  let pair := (d4OwnerCellEquiv m).symm cell
  have hmap : d4OwnerCellMap m pair = cell :=
    (d4OwnerCellEquiv m).apply_symm_apply cell
  have hcell : ownerCell pair.1.1 pair.1.2 = cell.1 :=
    congrArg Subtype.val hmap
  have hanchor :
      ownerAnchorForCell cell.1 pair.1.2 =
        (ownerQ pair.1.1, ownerR pair.1.1) := by
    rw [← hcell, ownerCell_eq_cellForOwnerAnchor]
    exact anchor_cell_roundtrip
      (ownerQ pair.1.1, ownerR pair.1.1) pair.1.2
  have hpairPhase :
      IsOwnerPhase (m + 2) (ownerAnchorForCell cell.1 pair.1.2) := by
    rw [hanchor]
    exact owner_anchor_is_phase pair.1.1
  have hlabel := phaseOwnerLabel_unique (m + 2) cell.1 pair.1.2 hpairPhase
  simp only [d4LiteralCellEnergy, phaseCellEnergy]
  change d4OwnerLabelEnergy pair.1.1 pair.1.2 = _
  rw [hlabel, hanchor]
  rfl

def d4LiteralPlacementEnergy {m : ℕ}
    (placement : D4LiteralPlacement m) : ℤ :=
  literalTileEnergy placement.tile placement.base.1 placement.base.2
    (placementBaseResidue (m + 2) placement.base)

theorem phase_energy_sum_of_d4_placement {m : ℕ}
    (placement : D4LiteralPlacement m) :
    (placement.cells.map (phaseCellEnergy (m + 2))).sum =
      d4LiteralPlacementEnergy placement := by
  change
    (((protoCells placement.tile).map
      (translateLocalCell placement.base)).map
      (phaseCellEnergy (m + 2))).sum = _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro localCell hlocal
  exact phaseCellEnergy_translate (m + 2) placement.base
    placement.tile localCell hlocal

end FiniteDefects
