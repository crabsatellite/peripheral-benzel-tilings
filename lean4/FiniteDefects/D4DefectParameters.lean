import FiniteDefects.D4ArmTriple

/-! # Literal parameter spaces for the five defect classes -/

namespace FiniteDefects

inductive D4DefectParameter (m : ℕ)
  | stone1 : SimplexPoint m → D4DefectParameter m
  | stone2 : SimplexPoint (m + 1) → D4DefectParameter m
  | boneA : SimplexPoint m → D4DefectParameter m
  | boneB : SimplexPoint m → D4DefectParameter m
  | boneC : SimplexPoint m → D4DefectParameter m

def D4DefectParameter.kind {m : ℕ} : D4DefectParameter m → D4DefectKind
  | .stone1 _ => .stone1
  | .stone2 _ => .stone2
  | .boneA _ => .boneA
  | .boneB _ => .boneB
  | .boneC _ => .boneC

def D4DefectParameter.core {m : ℕ} :
    D4DefectParameter m → MicroLabel → SimplexPoint (m + 2)
  | .stone1 p, .zero =>
      { u := p.u + 1, v := p.v, w := p.w + 1
        sum_eq := by have h := p.sum_eq; omega }
  | .stone1 p, .one =>
      { u := p.u + 1, v := p.v + 1, w := p.w
        sum_eq := by have h := p.sum_eq; omega }
  | .stone1 p, .two =>
      { u := p.u, v := p.v + 1, w := p.w + 1
        sum_eq := by have h := p.sum_eq; omega }
  | .stone2 p, .zero =>
      { u := p.u, v := p.v, w := p.w + 1
        sum_eq := by have h := p.sum_eq; omega }
  | .stone2 p, .one =>
      { u := p.u + 1, v := p.v, w := p.w
        sum_eq := by have h := p.sum_eq; omega }
  | .stone2 p, .two =>
      { u := p.u, v := p.v + 1, w := p.w
        sum_eq := by have h := p.sum_eq; omega }
  | .boneA p, .zero =>
      { u := p.u, v := p.v, w := p.w + 2
        sum_eq := by have h := p.sum_eq; omega }
  | .boneA p, .one =>
      { u := p.u + 1, v := p.v + 1, w := p.w
        sum_eq := by have h := p.sum_eq; omega }
  | .boneA p, .two =>
      { u := p.u, v := p.v + 1, w := p.w + 1
        sum_eq := by have h := p.sum_eq; omega }
  | .boneB p, .zero =>
      { u := p.u + 1, v := p.v, w := p.w + 1
        sum_eq := by have h := p.sum_eq; omega }
  | .boneB p, .one =>
      { u := p.u + 1, v := p.v + 1, w := p.w
        sum_eq := by have h := p.sum_eq; omega }
  | .boneB p, .two =>
      { u := p.u, v := p.v + 2, w := p.w
        sum_eq := by have h := p.sum_eq; omega }
  | .boneC p, .zero =>
      { u := p.u + 1, v := p.v, w := p.w + 1
        sum_eq := by have h := p.sum_eq; omega }
  | .boneC p, .one =>
      { u := p.u + 2, v := p.v, w := p.w
        sum_eq := by have h := p.sum_eq; omega }
  | .boneC p, .two =>
      { u := p.u, v := p.v + 1, w := p.w + 1
        sum_eq := by have h := p.sum_eq; omega }

def D4DefectParameter.base {m : ℕ} (parameter : D4DefectParameter m) : Cell :=
  (ownerQ (parameter.core .zero) - (parameter.kind.ownerShift .zero).1,
    ownerR (parameter.core .zero) - (parameter.kind.ownerShift .zero).2)

theorem D4DefectParameter.core_present {m : ℕ}
    (parameter : D4DefectParameter m) (label : MicroLabel) :
    inBenzel (m + 4) (2 * m + 4) (ownerCell (parameter.core label) label) := by
  rw [d4_owner_label_mem_iff]
  rcases parameter with p | p | p | p | p <;>
    rcases label with _ | _ | _ <;>
    simp [D4DefectParameter.core, d3k1LabelPresent] <;>
    have h := p.sum_eq <;> omega

theorem D4DefectParameter.local_cell_eq {m : ℕ}
    (parameter : D4DefectParameter m) (localCell : LocalCell)
    (hlocal : localCell ∈ protoCells parameter.kind.tile) :
    translateLocalCell parameter.base localCell =
      ownerCell (parameter.core
        (localLabel parameter.kind.residue localCell))
        (localLabel parameter.kind.residue localCell) := by
  rcases parameter with p | p | p | p | p <;>
    simp [D4DefectParameter.kind, D4DefectKind.tile, protoCells] at hlocal <;>
    rcases hlocal with rfl | rfl | rfl <;>
    simp [D4DefectParameter.base, D4DefectParameter.core,
      D4DefectParameter.kind, D4DefectKind.ownerShift,
      D4DefectKind.residue, localLabel, Res3.add, Res3.toLabel,
      translateLocalCell, ownerCell, ownerQ, ownerR,
      c00, c10, c20, c01, c02, c1m1, c2m2] <;> omega

noncomputable def D4DefectParameter.placement {m : ℕ}
    (parameter : D4DefectParameter m) : D4LiteralPlacement m := by
  let base := parameter.base
  have hall : ∀ localCell ∈ protoCells parameter.kind.tile,
      inBenzel (m + 4) (2 * m + 4)
        (translateLocalCell base localCell) := by
    intro localCell hlocal
    rw [show translateLocalCell base localCell =
        ownerCell (parameter.core
          (localLabel parameter.kind.residue localCell))
          (localLabel parameter.kind.residue localCell) by
      exact parameter.local_cell_eq localCell hlocal]
    exact parameter.core_present _
  have hc00 : c00 ∈ protoCells parameter.kind.tile := by
    rcases parameter <;> simp [D4DefectParameter.kind,
      D4DefectKind.tile, protoCells]
  have hbaseMem : inBenzel (m + 4) (2 * m + 4) base := by
    have h := hall c00 hc00
    simpa [base, translateLocalCell, c00] using h
  let baseCell : D4Cell m := ⟨base, hbaseMem⟩
  let candidate : D4PlacementCandidate m := (parameter.kind.tile, baseCell)
  exact ⟨candidate, by
    intro cell hcell
    change cell ∈ (protoCells parameter.kind.tile).map
      (translateLocalCell base) at hcell
    simp only [List.mem_map] at hcell
    obtain ⟨localCell, hlocal, rfl⟩ := hcell
    exact hall localCell hlocal⟩

@[simp] theorem D4DefectParameter.placement_tile {m : ℕ}
    (parameter : D4DefectParameter m) :
    parameter.placement.tile = parameter.kind.tile := rfl

@[simp] theorem D4DefectParameter.placement_base {m : ℕ}
    (parameter : D4DefectParameter m) :
    parameter.placement.base = parameter.base := rfl

theorem D4DefectParameter.base_residue {m : ℕ}
    (parameter : D4DefectParameter m) :
    placementBaseResidue (m + 2) parameter.base = parameter.kind.residue := by
  have hphase := owner_phase_identity (parameter.core .zero)
  rcases parameter with p | p | p | p | p <;>
    unfold D4DefectParameter.base placementBaseResidue residueOfInt <;>
    simp only [D4DefectParameter.core, D4DefectParameter.kind,
      D4DefectKind.ownerShift, D4DefectKind.residue, ownerQ, ownerR,
      Res3.value] at hphase ⊢ <;>
    split_ifs <;> simp_all <;> omega

theorem D4DefectParameter.placement_class {m : ℕ}
    (parameter : D4DefectParameter m) :
    D4IsDefectClass parameter.placement parameter.kind := by
  exact ⟨parameter.placement_tile, by
    rw [parameter.placement_base]
    exact parameter.base_residue⟩

theorem d4DefectClass_is_bad {m : ℕ} (placement : D4LiteralPlacement m)
    (kind : D4DefectKind) (hclass : D4IsDefectClass placement kind) :
    IsD4BadPlacement placement := by
  rcases kind with _ | _ | _ | _ | _
  · left
    exact ⟨hclass.1, by rw [hclass.2]; decide⟩
  · left
    exact ⟨hclass.1, by rw [hclass.2]; decide⟩
  · right
    simp [IsD4ThreeOwnerBone, D4DefectKind.tile,
      D4DefectKind.residue, hclass.1, hclass.2]
  · right
    simp [IsD4ThreeOwnerBone, D4DefectKind.tile,
      D4DefectKind.residue, hclass.1, hclass.2]
  · right
    simp [IsD4ThreeOwnerBone, D4DefectKind.tile,
      D4DefectKind.residue, hclass.1, hclass.2]

noncomputable def D4DefectParameter.defect {m : ℕ}
    (parameter : D4DefectParameter m) : D4DefectPlacement m :=
  ⟨parameter.placement,
    d4DefectClass_is_bad parameter.placement parameter.kind
      parameter.placement_class⟩

end FiniteDefects
