import FiniteDefects.D4DefectParameters

/-! # Equivalence between literal defect placements and the five simplex spaces -/

namespace FiniteDefects

theorem D4DefectParameter.core_anchor {m : ℕ}
    (parameter : D4DefectParameter m) (label : MicroLabel) :
    (ownerQ (parameter.core label), ownerR (parameter.core label)) =
      (parameter.base.1 + (parameter.kind.ownerShift label).1,
        parameter.base.2 + (parameter.kind.ownerShift label).2) := by
  rcases parameter with p | p | p | p | p <;>
    rcases label with _ | _ | _ <;>
    simp [D4DefectParameter.core, D4DefectParameter.base,
      D4DefectParameter.kind, D4DefectKind.ownerShift,
      ownerQ, ownerR] <;> omega

@[simp] theorem D4DefectParameter.defect_kind {m : ℕ}
    (parameter : D4DefectParameter m) :
    parameter.defect.kind = parameter.kind := by
  exact (exists_unique_d4DefectKind parameter.placement
    parameter.defect.2).choose_spec.2 parameter.kind
      parameter.placement_class |>.symm

theorem D4DefectParameter.defect_core {m : ℕ}
    (parameter : D4DefectParameter m) (label : MicroLabel) :
    parameter.defect.core label = parameter.core label := by
  apply simplex_eq_of_owner_anchor
  · have hleft := parameter.defect.core_anchor label
    have hright := parameter.core_anchor label
    rw [parameter.defect_kind] at hleft
    simp only [D4DefectParameter.defect, D4DefectParameter.placement_base] at hleft
    exact (congrArg Prod.fst hleft).trans (congrArg Prod.fst hright).symm
  · have hleft := parameter.defect.core_anchor label
    have hright := parameter.core_anchor label
    rw [parameter.defect_kind] at hleft
    simp only [D4DefectParameter.defect, D4DefectParameter.placement_base] at hleft
    exact (congrArg Prod.snd hleft).trans (congrArg Prod.snd hright).symm

noncomputable def D4DefectPlacement.stone1ParameterPoint {m : ℕ}
    (defect : D4DefectPlacement m) (hkind : defect.kind = .stone1) :
    SimplexPoint m := by
  have hzero := defect.core_anchor .zero
  have hone := defect.core_anchor .one
  have htwo := defect.core_anchor .two
  have hsumZero := (defect.core .zero).sum_eq
  have hsumOne := (defect.core .one).sum_eq
  have hsumTwo := (defect.core .two).sum_eq
  rw [hkind] at hzero hone htwo
  exact
    { u := (defect.core .two).u
      v := (defect.core .zero).v
      w := (defect.core .one).w
      sum_eq := by
        simp [D4DefectKind.ownerShift, ownerQ, ownerR] at hzero hone htwo
        omega }

noncomputable def D4DefectPlacement.stone2ParameterPoint {m : ℕ}
    (defect : D4DefectPlacement m) (hkind : defect.kind = .stone2) :
    SimplexPoint (m + 1) := by
  have hzero := defect.core_anchor .zero
  have hone := defect.core_anchor .one
  have htwo := defect.core_anchor .two
  have hsumZero := (defect.core .zero).sum_eq
  have hsumOne := (defect.core .one).sum_eq
  have hsumTwo := (defect.core .two).sum_eq
  rw [hkind] at hzero hone htwo
  exact
    { u := (defect.core .zero).u
      v := (defect.core .zero).v
      w := (defect.core .one).w
      sum_eq := by
        simp [D4DefectKind.ownerShift, ownerQ, ownerR] at hzero hone htwo
        omega }

noncomputable def D4DefectPlacement.boneAParameterPoint {m : ℕ}
    (defect : D4DefectPlacement m) (hkind : defect.kind = .boneA) :
    SimplexPoint m := by
  have hzero := defect.core_anchor .zero
  have hone := defect.core_anchor .one
  have htwo := defect.core_anchor .two
  have hsumZero := (defect.core .zero).sum_eq
  have hsumOne := (defect.core .one).sum_eq
  have hsumTwo := (defect.core .two).sum_eq
  rw [hkind] at hzero hone htwo
  exact
    { u := (defect.core .zero).u
      v := (defect.core .zero).v
      w := (defect.core .one).w
      sum_eq := by
        simp [D4DefectKind.ownerShift, ownerQ, ownerR] at hzero hone htwo
        omega }

noncomputable def D4DefectPlacement.boneBParameterPoint {m : ℕ}
    (defect : D4DefectPlacement m) (hkind : defect.kind = .boneB) :
    SimplexPoint m := by
  have hzero := defect.core_anchor .zero
  have hone := defect.core_anchor .one
  have htwo := defect.core_anchor .two
  have hsumZero := (defect.core .zero).sum_eq
  have hsumOne := (defect.core .one).sum_eq
  have hsumTwo := (defect.core .two).sum_eq
  rw [hkind] at hzero hone htwo
  exact
    { u := (defect.core .two).u
      v := (defect.core .zero).v
      w := (defect.core .one).w
      sum_eq := by
        simp [D4DefectKind.ownerShift, ownerQ, ownerR] at hzero hone htwo
        omega }

noncomputable def D4DefectPlacement.boneCParameterPoint {m : ℕ}
    (defect : D4DefectPlacement m) (hkind : defect.kind = .boneC) :
    SimplexPoint m := by
  have hzero := defect.core_anchor .zero
  have hone := defect.core_anchor .one
  have htwo := defect.core_anchor .two
  have hsumZero := (defect.core .zero).sum_eq
  have hsumOne := (defect.core .one).sum_eq
  have hsumTwo := (defect.core .two).sum_eq
  rw [hkind] at hzero hone htwo
  exact
    { u := (defect.core .two).u
      v := (defect.core .one).v
      w := (defect.core .one).w
      sum_eq := by
        simp [D4DefectKind.ownerShift, ownerQ, ownerR] at hzero hone htwo
        omega }

noncomputable def D4DefectPlacement.parameter {m : ℕ}
    (defect : D4DefectPlacement m) : D4DefectParameter m :=
  match hkind : defect.kind with
  | .stone1 => .stone1 (defect.stone1ParameterPoint hkind)
  | .stone2 => .stone2 (defect.stone2ParameterPoint hkind)
  | .boneA => .boneA (defect.boneAParameterPoint hkind)
  | .boneB => .boneB (defect.boneBParameterPoint hkind)
  | .boneC => .boneC (defect.boneCParameterPoint hkind)

@[simp] theorem D4DefectPlacement.parameter_kind {m : ℕ}
    (defect : D4DefectPlacement m) : defect.parameter.kind = defect.kind := by
  rw [D4DefectPlacement.parameter]
  split <;> rename_i hkind <;> exact hkind.symm

theorem D4DefectPlacement.parameter_core_zero {m : ℕ}
    (defect : D4DefectPlacement m) :
    defect.parameter.core .zero = defect.core .zero := by
  have hzero := defect.core_anchor .zero
  have hone := defect.core_anchor .one
  have htwo := defect.core_anchor .two
  have hsumZero := (defect.core .zero).sum_eq
  have hsumOne := (defect.core .one).sum_eq
  have hsumTwo := (defect.core .two).sum_eq
  rw [D4DefectPlacement.parameter]
  split <;> rename_i hkind <;>
    rw [hkind] at hzero hone htwo <;>
    apply simplexPoint_ext <;>
    simp only [D4DefectParameter.core,
      D4DefectPlacement.stone1ParameterPoint,
      D4DefectPlacement.stone2ParameterPoint,
      D4DefectPlacement.boneAParameterPoint,
      D4DefectPlacement.boneBParameterPoint,
      D4DefectPlacement.boneCParameterPoint] <;>
    simp [D4DefectKind.ownerShift, ownerQ, ownerR] at hzero hone htwo <;>
    omega

@[simp] theorem D4DefectPlacement.parameter_defect {m : ℕ}
    (defect : D4DefectPlacement m) : defect.parameter.defect = defect := by
  apply Subtype.ext
  change defect.parameter.placement = defect.1
  apply d4LiteralPlacement_ext_tile_base
  · rw [D4DefectParameter.placement_tile, defect.parameter_kind]
    exact defect.kind_spec.1.symm
  · rw [D4DefectParameter.placement_base, D4DefectParameter.base,
      defect.parameter_kind, defect.parameter_core_zero]
    have h := defect.core_anchor .zero
    apply Prod.ext
    · have hq := congrArg Prod.fst h
      simp only at hq ⊢
      omega
    · have hr := congrArg Prod.snd h
      simp only at hr ⊢
      omega

theorem D4DefectParameter.defect_injective {m : ℕ} :
    Function.Injective
      (D4DefectParameter.defect : D4DefectParameter m → D4DefectPlacement m) := by
  intro left right heq
  have hkind := congrArg D4DefectPlacement.kind heq
  rw [left.defect_kind, right.defect_kind] at hkind
  rcases left with p | p | p | p | p <;>
    rcases right with q | q | q | q | q <;>
    simp [D4DefectParameter.kind] at hkind
  all_goals
    have hzero := congrArg (fun defect : D4DefectPlacement m =>
      defect.core .zero) heq
    have hone := congrArg (fun defect : D4DefectPlacement m =>
      defect.core .one) heq
    have htwo := congrArg (fun defect : D4DefectPlacement m =>
      defect.core .two) heq
    dsimp only at hzero hone htwo
    rw [D4DefectParameter.defect_core,
      D4DefectParameter.defect_core] at hzero hone htwo
    congr 1
    apply simplexPoint_ext <;>
      simp [D4DefectParameter.core] at hzero hone htwo ⊢ <;>
      omega

@[simp] theorem D4DefectParameter.defect_parameter {m : ℕ}
    (parameter : D4DefectParameter m) : parameter.defect.parameter = parameter := by
  apply D4DefectParameter.defect_injective
  exact D4DefectPlacement.parameter_defect parameter.defect

noncomputable def d4DefectPlacementEquivParameter (m : ℕ) :
    D4DefectPlacement m ≃ D4DefectParameter m where
  toFun := D4DefectPlacement.parameter
  invFun := D4DefectParameter.defect
  left_inv := D4DefectPlacement.parameter_defect
  right_inv := D4DefectParameter.defect_parameter

end FiniteDefects
