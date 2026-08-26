import FiniteDefects.D4PlacementOwners

/-! # The three labelled owners touched by the unique defect -/

namespace FiniteDefects

def D4DefectKind.localCell : D4DefectKind → MicroLabel → LocalCell
  | .stone1, .zero => c01
  | .stone1, .one => c00
  | .stone1, .two => c10
  | .stone2, .zero => c10
  | .stone2, .one => c01
  | .stone2, .two => c00
  | .boneA, .zero => c20
  | .boneA, .one => c00
  | .boneA, .two => c10
  | .boneB, .zero => c02
  | .boneB, .one => c01
  | .boneB, .two => c00
  | .boneC, .zero => c1m1
  | .boneC, .one => c00
  | .boneC, .two => c2m2

theorem D4DefectKind.localCell_mem (kind : D4DefectKind)
    (label : MicroLabel) :
    kind.localCell label ∈ protoCells kind.tile := by
  rcases kind <;> rcases label <;> decide

theorem D4DefectKind.localCell_label (kind : D4DefectKind)
    (label : MicroLabel) :
    localLabel kind.residue (kind.localCell label) = label := by
  rcases kind <;> rcases label <;> decide

noncomputable def d4DefectLocalCell {m : ℕ} (tiling : D4LiteralTiling m)
    (label : MicroLabel) : D4PlacementLocalCell (d4BadPlacement tiling) :=
  ⟨(d4DefectKind tiling).localCell label, by
    rw [(d4DefectKind_spec tiling).1]
    exact D4DefectKind.localCell_mem (d4DefectKind tiling) label⟩

noncomputable def d4DefectCorePair {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    PresentD4OwnerLabel m :=
  d4OwnerPairOfLocal (d4BadPlacement tiling)
    (d4DefectLocalCell tiling label)

noncomputable def d4DefectCore {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    SimplexPoint (m + 2) :=
  (d4DefectCorePair tiling label).1.1

theorem d4DefectCorePair_label {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    (d4DefectCorePair tiling label).1.2 = label := by
  rw [d4DefectCorePair, d4OwnerPairOfLocal_label]
  rw [(d4DefectKind_spec tiling).2]
  exact D4DefectKind.localCell_label (d4DefectKind tiling) label

theorem d4DefectCore_cell {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    ownerCell (d4DefectCore tiling label) label =
      d4RawCellOfLocal (d4BadPlacement tiling)
        (d4DefectLocalCell tiling label) := by
  have h := d4OwnerPairOfLocal_cell (d4BadPlacement tiling)
    (d4DefectLocalCell tiling label)
  have hl := d4DefectCorePair_label tiling label
  unfold d4DefectCorePair at hl
  rw [hl] at h
  unfold d4DefectCore d4DefectCorePair
  exact h

theorem d4DefectCore_present {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    inBenzel (m + 4) (2 * m + 4)
      (ownerCell (d4DefectCore tiling label) label) := by
  rw [d4DefectCore_cell]
  exact (d4CellOfLocal (d4BadPlacement tiling)
    (d4DefectLocalCell tiling label)).2

theorem d4_defect_local_unique_by_label
    (kind : D4DefectKind) (label : MicroLabel) (localCell : LocalCell)
    (hmem : localCell ∈ protoCells kind.tile)
    (hlabel : localLabel kind.residue localCell = label) :
    localCell = kind.localCell label := by
  rcases kind <;> rcases label <;>
    simp [D4DefectKind.tile, protoCells] at hmem <;>
    rcases hmem with rfl | rfl | rfl <;>
    simp [D4DefectKind.residue, localLabel, Res3.add, Res3.toLabel,
      c00, c10, c20, c01, c02, c1m1, c2m2,
      D4DefectKind.localCell] at hlabel ⊢

theorem d4_bad_placement_local_is_core {m : ℕ}
    (tiling : D4LiteralTiling m)
    (localCell : D4PlacementLocalCell (d4BadPlacement tiling)) :
    (d4OwnerPairOfLocal (d4BadPlacement tiling) localCell).1.1 =
      d4DefectCore tiling
        (d4OwnerPairOfLocal (d4BadPlacement tiling) localCell).1.2 := by
  let kind := d4DefectKind tiling
  let label :=
    (d4OwnerPairOfLocal (d4BadPlacement tiling) localCell).1.2
  have htile := (d4DefectKind_spec tiling).1
  have hrho := (d4DefectKind_spec tiling).2
  have hlocalMem : localCell.1 ∈ protoCells kind.tile := by
    rw [← htile]
    exact localCell.2
  have hlocalLabel : localLabel kind.residue localCell.1 = label := by
    rw [← hrho]
    exact (d4OwnerPairOfLocal_label (d4BadPlacement tiling) localCell).symm
  have hlocal := d4_defect_local_unique_by_label kind label localCell.1
    hlocalMem hlocalLabel
  have hsub : localCell = d4DefectLocalCell tiling label := by
    apply Subtype.ext
    exact hlocal
  unfold d4DefectCore d4DefectCorePair
  exact congrArg
    (fun lc => (d4OwnerPairOfLocal (d4BadPlacement tiling) lc).1.1)
    hsub

def D4DefectKind.ownerShift : D4DefectKind → MicroLabel → Cell
  | .stone1, .zero => (0, 1)
  | .stone1, .one => (-1, 0)
  | .stone1, .two => (1, -1)
  | .stone2, .zero => (1, 0)
  | .stone2, .one => (-1, 1)
  | .stone2, .two => (0, -1)
  | .boneA, .zero => (2, 0)
  | .boneA, .one => (-1, 0)
  | .boneA, .two => (1, -1)
  | .boneB, .zero => (0, 2)
  | .boneB, .one => (-1, 1)
  | .boneB, .two => (0, -1)
  | .boneC, .zero => (1, -1)
  | .boneC, .one => (-1, 0)
  | .boneC, .two => (2, -3)

theorem D4DefectKind.ownerShift_eq (kind : D4DefectKind)
    (label : MicroLabel) :
    FiniteDefects.ownerShift kind.residue (kind.localCell label) =
      kind.ownerShift label := by
  rcases kind <;> rcases label <;> decide

theorem D4DefectKind.ownerShift_injective (kind : D4DefectKind) :
    Function.Injective kind.ownerShift := by
  intro left right h
  rcases kind <;> rcases left <;> rcases right <;> simp_all [D4DefectKind.ownerShift]

theorem d4DefectCore_anchor {m : ℕ} (tiling : D4LiteralTiling m)
    (label : MicroLabel) :
    (ownerQ (d4DefectCore tiling label),
      ownerR (d4DefectCore tiling label)) =
      ((d4BadPlacement tiling).base.1 +
          ((d4DefectKind tiling).ownerShift label).1,
        (d4BadPlacement tiling).base.2 +
          ((d4DefectKind tiling).ownerShift label).2) := by
  have h := d4OwnerPairOfLocal_anchor (d4BadPlacement tiling)
    (d4DefectLocalCell tiling label)
  rw [(d4DefectKind_spec tiling).2] at h
  change _ =
    ((d4BadPlacement tiling).base.1 +
        (FiniteDefects.ownerShift (d4DefectKind tiling).residue
          ((d4DefectKind tiling).localCell label)).1,
      (d4BadPlacement tiling).base.2 +
        (FiniteDefects.ownerShift (d4DefectKind tiling).residue
          ((d4DefectKind tiling).localCell label)).2) at h
  rw [D4DefectKind.ownerShift_eq] at h
  unfold d4DefectCore d4DefectCorePair
  exact h

theorem d4DefectCore_distinct {m : ℕ} (tiling : D4LiteralTiling m)
    {left right : MicroLabel} (hne : left ≠ right) :
    d4DefectCore tiling left ≠ d4DefectCore tiling right := by
  intro hcore
  have hleft := d4DefectCore_anchor tiling left
  have hright := d4DefectCore_anchor tiling right
  rw [hcore] at hleft
  have hshifts : (d4DefectKind tiling).ownerShift left =
      (d4DefectKind tiling).ownerShift right := by
    apply Prod.ext
    · have hl := congrArg Prod.fst hleft
      have hr := congrArg Prod.fst hright
      simp at hl hr ⊢
      omega
    · have hl := congrArg Prod.snd hleft
      have hr := congrArg Prod.snd hright
      simp at hl hr ⊢
      omega
  exact hne ((D4DefectKind.ownerShift_injective
    (d4DefectKind tiling)) hshifts)

end FiniteDefects
