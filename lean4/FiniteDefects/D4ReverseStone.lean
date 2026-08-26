import FiniteDefects.D4PathSeparation

/-! # Reconstructing an in-phase stone at one unused full owner -/

namespace FiniteDefects

theorem d4Stone_local_cell_eq_owner {t : ℕ} (owner : SimplexPoint t)
    (localCell : LocalCell) (hlocal : localCell ∈ protoCells .stone) :
    translateLocalCell (ownerQ owner, ownerR owner) localCell =
      ownerCell owner (localLabel .r0 localCell) := by
  rw [ownerCell_eq_cellForOwnerAnchor]
  simp [protoCells] at hlocal
  rcases hlocal with rfl | rfl | rfl <;>
    simp [translateLocalCell, localLabel, Res3.add, Res3.toLabel,
      cellForOwnerAnchor, c00, c10, c01]

noncomputable def d4ReverseStonePlacement {m : ℕ}
    (owner : SimplexPoint (m + 2)) (hfull : IsD4FullOwner owner) :
    D4LiteralPlacement m := by
  let base : Cell := (ownerQ owner, ownerR owner)
  have hall : ∀ localCell ∈ protoCells .stone,
      inBenzel (m + 4) (2 * m + 4)
        (translateLocalCell base localCell) := by
    intro localCell hlocal
    rw [d4Stone_local_cell_eq_owner owner localCell hlocal]
    exact hfull (localLabel .r0 localCell)
  have hbaseMem : inBenzel (m + 4) (2 * m + 4) base := by
    have h := hall c00 (by simp [protoCells])
    simpa [base, translateLocalCell, c00] using h
  let baseCell : D4Cell m := ⟨base, hbaseMem⟩
  let candidate : D4PlacementCandidate m := (.stone, baseCell)
  exact ⟨candidate, by
    intro cell hcell
    change cell ∈ (protoCells .stone).map (translateLocalCell base) at hcell
    simp only [List.mem_map] at hcell
    obtain ⟨localCell, hlocal, rfl⟩ := hcell
    exact hall localCell hlocal⟩

@[simp] theorem d4ReverseStonePlacement_tile {m : ℕ}
    (owner : SimplexPoint (m + 2)) (hfull : IsD4FullOwner owner) :
    (d4ReverseStonePlacement owner hfull).tile = .stone := rfl

@[simp] theorem d4ReverseStonePlacement_base {m : ℕ}
    (owner : SimplexPoint (m + 2)) (hfull : IsD4FullOwner owner) :
    (d4ReverseStonePlacement owner hfull).base = (ownerQ owner, ownerR owner) :=
  rfl

theorem d4ReverseStonePlacement_covers {m : ℕ}
    (owner : SimplexPoint (m + 2)) (hfull : IsD4FullOwner owner)
    (label : MicroLabel) :
    D4PlacementCovers (d4ReverseStonePlacement owner hfull)
      ⟨ownerCell owner label, hfull label⟩ := by
  unfold D4PlacementCovers
  change ownerCell owner label ∈
    (protoCells .stone).map
      (translateLocalCell (ownerQ owner, ownerR owner))
  rcases label
  · rw [show ownerCell owner .zero =
      translateLocalCell (ownerQ owner, ownerR owner) c00 by
        simp [ownerCell, translateLocalCell, c00]]
    simp [protoCells]
  · rw [show ownerCell owner .one =
      translateLocalCell (ownerQ owner, ownerR owner) c10 by
        simp [ownerCell, translateLocalCell, c10]]
    simp [protoCells]
  · rw [show ownerCell owner .two =
      translateLocalCell (ownerQ owner, ownerR owner) c01 by
        simp [ownerCell, translateLocalCell, c01]]
    simp [protoCells]

theorem d4ReverseStonePlacement_cover_role {m : ℕ}
    (owner : SimplexPoint (m + 2)) (hfull : IsD4FullOwner owner)
    (cell : Cell)
    (hcover : cell ∈ (d4ReverseStonePlacement owner hfull).cells) :
    ∃ label, cell = ownerCell owner label := by
  change cell ∈ (protoCells .stone).map
    (translateLocalCell (ownerQ owner, ownerR owner)) at hcover
  simp only [List.mem_map] at hcover
  obtain ⟨localCell, hlocal, rfl⟩ := hcover
  exact ⟨localLabel .r0 localCell,
    d4Stone_local_cell_eq_owner owner localCell hlocal⟩

theorem d4ReverseStonePlacement_phase {m : ℕ}
    (owner : SimplexPoint (m + 2)) (hfull : IsD4FullOwner owner) :
    placementBaseResidue (m + 2)
      (d4ReverseStonePlacement owner hfull).base = .r0 := by
  have hphase := owner_anchor_is_phase owner
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphase
  have hdiv : (3 : ℤ) ∣ ownerQ owner - ownerR owner - (m + 2 : ℤ) := by
    have hneg := dvd_neg.mpr hphase
    have hcast : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by omega
    simpa [hcast] using hneg
  have hmod : (ownerQ owner - ownerR owner - (m + 2 : ℤ)) % 3 = 0 := by
    exact Int.dvd_iff_emod_eq_zero.mp hdiv
  simp [placementBaseResidue, residueOfInt, hmod]

theorem d4InPhaseStone_base_eq_owner {m : ℕ}
    (placement : D4LiteralPlacement m) (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0) :
    placement.base =
      (ownerQ (d4StoneOwner placement htile),
        ownerR (d4StoneOwner placement htile)) := by
  have hanchor := d4OwnerPairOfLocal_anchor placement
    (d4StoneLocal placement htile .zero)
  rw [hphase] at hanchor
  simp [d4StoneLocal, d4StoneLocalForLabel, ownerShift, localLabel,
    Res3.add, Res3.toLabel, c00] at hanchor
  exact hanchor.symm

theorem d4ReverseStonePlacement_eq_inPhase {m : ℕ}
    (placement : D4LiteralPlacement m) (htile : placement.tile = .stone)
    (hphase : placementBaseResidue (m + 2) placement.base = .r0) :
    d4ReverseStonePlacement (d4StoneOwner placement htile)
      (d4StoneOwner_full placement htile hphase) = placement := by
  apply Subtype.ext
  apply Prod.ext
  · exact htile.symm
  · apply Subtype.ext
    exact (d4InPhaseStone_base_eq_owner placement htile hphase).symm

end FiniteDefects
