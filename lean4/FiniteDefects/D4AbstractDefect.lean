import FiniteDefects.D4CoreSeparation

/-! # Defect placements and their labelled cores independent of a tiling -/

namespace FiniteDefects

abbrev D4DefectPlacement (m : ℕ) :=
  {placement : D4LiteralPlacement m // IsD4BadPlacement placement}

noncomputable def D4DefectPlacement.kind {m : ℕ}
    (defect : D4DefectPlacement m) : D4DefectKind :=
  (exists_unique_d4DefectKind defect.1 defect.2).choose

theorem D4DefectPlacement.kind_spec {m : ℕ}
    (defect : D4DefectPlacement m) :
    D4IsDefectClass defect.1 defect.kind :=
  (exists_unique_d4DefectKind defect.1 defect.2).choose_spec.1

noncomputable def D4DefectPlacement.localCell {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    D4PlacementLocalCell defect.1 :=
  ⟨defect.kind.localCell label, by
    rw [defect.kind_spec.1]
    exact D4DefectKind.localCell_mem defect.kind label⟩

noncomputable def D4DefectPlacement.corePair {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    PresentD4OwnerLabel m :=
  d4OwnerPairOfLocal defect.1 (defect.localCell label)

noncomputable def D4DefectPlacement.core {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    SimplexPoint (m + 2) := (defect.corePair label).1.1

theorem D4DefectPlacement.corePair_label {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    (defect.corePair label).1.2 = label := by
  rw [D4DefectPlacement.corePair, d4OwnerPairOfLocal_label]
  rw [defect.kind_spec.2]
  exact D4DefectKind.localCell_label defect.kind label

theorem D4DefectPlacement.core_cell {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    ownerCell (defect.core label) label =
      d4RawCellOfLocal defect.1 (defect.localCell label) := by
  have h := d4OwnerPairOfLocal_cell defect.1 (defect.localCell label)
  have hl := defect.corePair_label label
  unfold D4DefectPlacement.corePair at hl
  rw [hl] at h
  exact h

theorem D4DefectPlacement.core_present {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    inBenzel (m + 4) (2 * m + 4)
      (ownerCell (defect.core label) label) := by
  rw [defect.core_cell]
  exact (d4CellOfLocal defect.1 (defect.localCell label)).2

theorem D4DefectPlacement.covers_core {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    D4PlacementCovers defect.1
      ⟨ownerCell (defect.core label) label, defect.core_present label⟩ := by
  unfold D4PlacementCovers
  change ownerCell (defect.core label) label ∈ defect.1.cells
  rw [defect.core_cell]
  simp only [D4LiteralPlacement.cells, d4PlacementCellList, List.mem_map]
  exact ⟨defect.kind.localCell label, by
    change defect.kind.localCell label ∈ protoCells defect.1.tile
    rw [defect.kind_spec.1]
    exact D4DefectKind.localCell_mem defect.kind label, rfl⟩

theorem D4DefectPlacement.local_is_core {m : ℕ}
    (defect : D4DefectPlacement m)
    (localCell : D4PlacementLocalCell defect.1) :
    (d4OwnerPairOfLocal defect.1 localCell).1.1 =
      defect.core (d4OwnerPairOfLocal defect.1 localCell).1.2 := by
  let label := (d4OwnerPairOfLocal defect.1 localCell).1.2
  have hmem : localCell.1 ∈ protoCells defect.kind.tile := by
    rw [← defect.kind_spec.1]
    exact localCell.2
  have hlabel : localLabel defect.kind.residue localCell.1 = label := by
    rw [← defect.kind_spec.2]
    exact (d4OwnerPairOfLocal_label defect.1 localCell).symm
  have hlocal := d4_defect_local_unique_by_label defect.kind label
    localCell.1 hmem hlabel
  have hsub : localCell = defect.localCell label := by
    apply Subtype.ext
    exact hlocal
  unfold D4DefectPlacement.core D4DefectPlacement.corePair
  exact congrArg (fun lc => (d4OwnerPairOfLocal defect.1 lc).1.1) hsub

theorem D4DefectPlacement.cover_is_core {m : ℕ}
    (defect : D4DefectPlacement m) (p : SimplexPoint (m + 2))
    (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label))
    (hcover : D4PlacementCovers defect.1 ⟨ownerCell p label, hpresent⟩) :
    p = defect.core label := by
  obtain ⟨localCell, hraw⟩ := exists_d4LocalCell_of_cover defect.1
    ⟨ownerCell p label, hpresent⟩ hcover
  have hpair := d4OwnerPairOfLocal_eq_of_rawCell defect.1 localCell p label hraw
  have hcore := defect.local_is_core localCell
  rw [hpair.2] at hcore
  exact hpair.1.symm.trans hcore

theorem D4DefectPlacement.core_anchor {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    (ownerQ (defect.core label), ownerR (defect.core label)) =
      (defect.1.base.1 + (defect.kind.ownerShift label).1,
        defect.1.base.2 + (defect.kind.ownerShift label).2) := by
  have h := d4OwnerPairOfLocal_anchor defect.1 (defect.localCell label)
  rw [defect.kind_spec.2] at h
  change _ =
    (defect.1.base.1 +
        (FiniteDefects.ownerShift defect.kind.residue
          (defect.kind.localCell label)).1,
      defect.1.base.2 +
        (FiniteDefects.ownerShift defect.kind.residue
          (defect.kind.localCell label)).2) at h
  rw [D4DefectKind.ownerShift_eq] at h
  exact h

theorem D4DefectPlacement.core_zero_w_gt_one {m : ℕ}
    (defect : D4DefectPlacement m) :
    (defect.core .one).w < (defect.core .zero).w := by
  have hzero := defect.core_anchor .zero
  have hone := defect.core_anchor .one
  have hwzero := recover_w_numerator (defect.core .zero)
  have hwone := recover_w_numerator (defect.core .one)
  generalize hk : defect.kind = kind at hzero hone
  rcases kind <;> simp [D4DefectKind.ownerShift] at hzero hone
  all_goals rcases hzero with ⟨hzq, hzr⟩
  all_goals rcases hone with ⟨hoq, hor⟩
  all_goals omega

theorem D4DefectPlacement.core_one_u_gt_two {m : ℕ}
    (defect : D4DefectPlacement m) :
    (defect.core .two).u < (defect.core .one).u := by
  have hone := defect.core_anchor .one
  have htwo := defect.core_anchor .two
  have huone := recover_u_numerator (defect.core .one)
  have hutwo := recover_u_numerator (defect.core .two)
  generalize hk : defect.kind = kind at hone htwo
  rcases kind <;> simp [D4DefectKind.ownerShift] at hone htwo
  all_goals rcases hone with ⟨hoq, hor⟩
  all_goals rcases htwo with ⟨htq, htr⟩
  all_goals omega

theorem D4DefectPlacement.core_two_v_gt_zero {m : ℕ}
    (defect : D4DefectPlacement m) :
    (defect.core .zero).v < (defect.core .two).v := by
  have hzero := defect.core_anchor .zero
  have htwo := defect.core_anchor .two
  have hvzero := recover_v_numerator (defect.core .zero)
  have hvtwo := recover_v_numerator (defect.core .two)
  generalize hk : defect.kind = kind at hzero htwo
  rcases kind <;> simp [D4DefectKind.ownerShift] at hzero htwo
  all_goals rcases hzero with ⟨hzq, hzr⟩
  all_goals rcases htwo with ⟨htq, htr⟩
  all_goals omega

noncomputable def d4TilingDefect {m : ℕ}
    (tiling : D4LiteralTiling m) : D4DefectPlacement m :=
  ⟨d4BadPlacement tiling, d4BadPlacement_isBad tiling⟩

theorem d4TilingDefect_kind {m : ℕ} (tiling : D4LiteralTiling m) :
    (d4TilingDefect tiling).kind = d4DefectKind tiling := by
  exact (exists_unique_d4DefectKind (d4BadPlacement tiling)
    (d4BadPlacement_isBad tiling)).choose_spec.2 _ (d4DefectKind_spec tiling)

theorem d4TilingDefect_core {m : ℕ} (tiling : D4LiteralTiling m)
    (label : MicroLabel) :
    (d4TilingDefect tiling).core label = d4DefectCore tiling label := by
  have hlocal : (d4TilingDefect tiling).localCell label =
      d4DefectLocalCell tiling label := by
    apply Subtype.ext
    exact congrArg (fun kind : D4DefectKind => kind.localCell label)
      (d4TilingDefect_kind tiling)
  unfold D4DefectPlacement.core D4DefectPlacement.corePair
  unfold d4DefectCore d4DefectCorePair
  rw [hlocal]
  rfl

end FiniteDefects
