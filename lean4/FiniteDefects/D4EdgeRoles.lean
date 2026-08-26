import FiniteDefects.D4DefectCores

/-! # Literal owner roles of every good-bone cell -/

namespace FiniteDefects

theorem simplex_eq_of_owner_anchor {t : ℕ} {p q : SimplexPoint t}
    (hq : ownerQ p = ownerQ q) (hr : ownerR p = ownerR q) : p = q := by
  apply simplexPoint_ext
  all_goals
    have hu := recover_u_numerator p
    have hu' := recover_u_numerator q
    have hv := recover_v_numerator p
    have hv' := recover_v_numerator q
    have hw := recover_w_numerator p
    have hw' := recover_w_numerator q
    omega

theorem d4LocalOwner_eq_edge_source {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (localCell : D4PlacementLocalCell edge.placement)
    (hshift :
      FiniteDefects.ownerShift
        (placementBaseResidue (m + 2) edge.placement.base) localCell.1 =
        edge.boneClass.sourceShift) :
    (d4OwnerPairOfLocal edge.placement localCell).1.1 = edge.source := by
  have hanchor := d4OwnerPairOfLocal_anchor edge.placement localCell
  apply simplex_eq_of_owner_anchor
  · have h := congrArg Prod.fst hanchor
    rw [hshift] at h
    exact h.trans edge.source_anchor.1.symm
  · have h := congrArg Prod.snd hanchor
    rw [hshift] at h
    exact h.trans edge.source_anchor.2.symm

theorem d4LocalOwner_eq_edge_target {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (localCell : D4PlacementLocalCell edge.placement)
    (hshift :
      FiniteDefects.ownerShift
        (placementBaseResidue (m + 2) edge.placement.base) localCell.1 =
        edge.boneClass.targetShift) :
    (d4OwnerPairOfLocal edge.placement localCell).1.1 = edge.target := by
  have hanchor := d4OwnerPairOfLocal_anchor edge.placement localCell
  apply simplex_eq_of_owner_anchor
  · have h := congrArg Prod.fst hanchor
    rw [hshift] at h
    exact h.trans edge.target_anchor.1.symm
  · have h := congrArg Prod.snd hanchor
    rw [hshift] at h
    exact h.trans edge.target_anchor.2.symm

theorem d4GoodEdge_local_role {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (localCell : D4PlacementLocalCell edge.placement) :
    ((d4OwnerPairOfLocal edge.placement localCell).1.1 = edge.source ∧
      (d4OwnerPairOfLocal edge.placement localCell).1.2 ≠
        edge.boneClass.label) ∨
    ((d4OwnerPairOfLocal edge.placement localCell).1.1 = edge.target ∧
      (d4OwnerPairOfLocal edge.placement localCell).1.2 =
        edge.boneClass.label) := by
  rcases localCell with ⟨localCell, hlocalMem⟩
  have htile := edge.class_spec.1
  have hrho := edge.class_spec.2
  have hmem : localCell ∈ protoCells edge.boneClass.tile := by
    rw [← htile]
    exact hlocalMem
  by_cases htarget : localCell = edge.boneClass.targetWitnessCell
  · right
    have hshift :
        FiniteDefects.ownerShift
          (placementBaseResidue (m + 2) edge.placement.base) localCell =
          edge.boneClass.targetShift := by
      rw [hrho, htarget]
      rcases edge.boneClass <;> decide
    refine ⟨d4LocalOwner_eq_edge_target edge ⟨localCell, hlocalMem⟩ hshift, ?_⟩
    rw [d4OwnerPairOfLocal_label, hrho]
    change localLabel edge.boneClass.residue localCell = edge.boneClass.label
    rw [htarget]
    rcases edge.boneClass <;> decide
  · left
    have hsourceDatum :
        FiniteDefects.ownerShift edge.boneClass.residue localCell =
            edge.boneClass.sourceShift ∧
          localLabel edge.boneClass.residue localCell ≠
            edge.boneClass.label := by
      rcases hc : edge.boneClass with _ | _ | _ | _ | _ | _
      all_goals
        simp only [hc, GoodBoneClass.tile, protoCells, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hmem
      all_goals rcases hmem with rfl | rfl | rfl
      all_goals
        simp [hc, GoodBoneClass.residue, GoodBoneClass.sourceShift,
          GoodBoneClass.targetWitnessCell, GoodBoneClass.label,
          ownerShift, localLabel, Res3.add, Res3.toLabel,
          c00, c10, c20, c01, c02, c1m1, c2m2] at htarget ⊢
    have hshift :
        FiniteDefects.ownerShift
          (placementBaseResidue (m + 2) edge.placement.base) localCell =
          edge.boneClass.sourceShift := by
      rw [hrho]
      exact hsourceDatum.1
    refine ⟨d4LocalOwner_eq_edge_source edge ⟨localCell, hlocalMem⟩ hshift, ?_⟩
    rw [d4OwnerPairOfLocal_label, hrho]
    change localLabel edge.boneClass.residue localCell ≠ edge.boneClass.label
    exact hsourceDatum.2

theorem d4GoodEdge_label_allowed {m : ℕ}
    (edge : D4LiteralDirectedEdge m) :
    allowedStep edge.boneClass.label edge.boneClass.step :=
  goodBoneClass_step_allowed edge.boneClass

theorem d4GoodEdge_source_ne_target {m : ℕ}
    (edge : D4LiteralDirectedEdge m) : edge.source ≠ edge.target := by
  intro heq
  rcases d4LiteralDirectedEdge_simplex_step edge with hA | hB | hC
  · rw [heq] at hA
    omega
  · rw [heq] at hB
    omega
  · rw [heq] at hC
    omega

theorem D4LiteralDirectedEdge.ext_of_placement {m : ℕ}
    (left right : D4LiteralDirectedEdge m)
    (hplacement : left.placement = right.placement) : left = right := by
  rcases left with ⟨placement, leftClass, leftSpec, leftSource,
    leftTarget, leftSourceAnchor, leftTargetAnchor⟩
  rcases right with ⟨rightPlacement, rightClass, rightSpec, rightSource,
    rightTarget, rightSourceAnchor, rightTargetAnchor⟩
  dsimp at hplacement
  subst rightPlacement
  have hclass : leftClass = rightClass := by
    rcases leftClass <;> rcases rightClass <;>
      simp_all [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue]
  subst rightClass
  have hsource : leftSource = rightSource := by
    apply simplex_eq_of_owner_anchor
    · rw [leftSourceAnchor.1, rightSourceAnchor.1]
    · rw [leftSourceAnchor.2, rightSourceAnchor.2]
  subst rightSource
  have htarget : leftTarget = rightTarget := by
    apply simplex_eq_of_owner_anchor
    · rw [leftTargetAnchor.1, rightTargetAnchor.1]
    · rw [leftTargetAnchor.2, rightTargetAnchor.2]
  subst rightTarget
  rfl

theorem d4LiteralDirectedEdge_is_bone {m : ℕ}
    (edge : D4LiteralDirectedEdge m) : edge.placement.tile ≠ .stone := by
  rw [edge.class_spec.1]
  rcases edge.boneClass <;> decide

theorem d4LiteralDirectedEdge_not_three_owner {m : ℕ}
    (edge : D4LiteralDirectedEdge m) :
    ¬IsD4ThreeOwnerBone edge.placement := by
  unfold IsD4ThreeOwnerBone
  rw [edge.class_spec.1, edge.class_spec.2]
  rcases edge.boneClass <;>
    simp [IsD4ThreeOwnerBone, GoodBoneClass.tile, GoodBoneClass.residue]

def GoodBoneClass.localCellForLabel : GoodBoneClass → MicroLabel → LocalCell
  | .boneA0, .zero => c00
  | .boneA0, .one => c10
  | .boneA0, .two => c20
  | .boneA2, .zero => c10
  | .boneA2, .one => c20
  | .boneA2, .two => c00
  | .boneB0, .zero => c00
  | .boneB0, .one => c02
  | .boneB0, .two => c01
  | .boneB1, .zero => c01
  | .boneB1, .one => c00
  | .boneB1, .two => c02
  | .boneC0, .zero => c00
  | .boneC0, .one => c2m2
  | .boneC0, .two => c1m1
  | .boneC2, .zero => c2m2
  | .boneC2, .one => c1m1
  | .boneC2, .two => c00

theorem GoodBoneClass.localCellForLabel_mem (boneClass : GoodBoneClass)
    (label : MicroLabel) :
    boneClass.localCellForLabel label ∈ protoCells boneClass.tile := by
  rcases boneClass <;> rcases label <;> decide

theorem GoodBoneClass.localCellForLabel_label (boneClass : GoodBoneClass)
    (label : MicroLabel) :
    localLabel boneClass.residue (boneClass.localCellForLabel label) =
      label := by
  rcases boneClass <;> rcases label <;> decide

theorem GoodBoneClass.localCellForLabel_shift (boneClass : GoodBoneClass)
    (label : MicroLabel) :
    FiniteDefects.ownerShift boneClass.residue
        (boneClass.localCellForLabel label) =
      if label = boneClass.label then boneClass.targetShift
      else boneClass.sourceShift := by
  rcases boneClass <;> rcases label <;> decide

theorem goodBoneClass_cell_role (boneClass : GoodBoneClass)
    (localCell : LocalCell) (hmem : localCell ∈ protoCells boneClass.tile) :
    (FiniteDefects.ownerShift boneClass.residue localCell =
        boneClass.sourceShift ∧
      localLabel boneClass.residue localCell ≠ boneClass.label) ∨
    (FiniteDefects.ownerShift boneClass.residue localCell =
        boneClass.targetShift ∧
      localLabel boneClass.residue localCell = boneClass.label) := by
  rcases hc : boneClass with _ | _ | _ | _ | _ | _
  all_goals
    simp only [hc, GoodBoneClass.tile, protoCells, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hmem
  all_goals rcases hmem with rfl | rfl | rfl
  all_goals
    simp [hc, GoodBoneClass.residue, GoodBoneClass.sourceShift,
      GoodBoneClass.targetShift, GoodBoneClass.label,
      ownerShift, localLabel, Res3.add, Res3.toLabel,
      c00, c10, c20, c01, c02, c1m1, c2m2, stepA, stepC]

def d4GoodEdgeLocalForLabel {m : ℕ} (edge : D4LiteralDirectedEdge m)
    (label : MicroLabel) : D4PlacementLocalCell edge.placement :=
  ⟨edge.boneClass.localCellForLabel label, by
    rw [edge.class_spec.1]
    exact GoodBoneClass.localCellForLabel_mem edge.boneClass label⟩

theorem d4GoodEdgeLocalForLabel_pair {m : ℕ}
    (edge : D4LiteralDirectedEdge m) (label : MicroLabel) :
    (d4OwnerPairOfLocal edge.placement
        (d4GoodEdgeLocalForLabel edge label)).1.2 = label ∧
      (d4OwnerPairOfLocal edge.placement
        (d4GoodEdgeLocalForLabel edge label)).1.1 =
        if label = edge.boneClass.label then edge.target else edge.source := by
  constructor
  · rw [d4OwnerPairOfLocal_label, edge.class_spec.2]
    exact GoodBoneClass.localCellForLabel_label edge.boneClass label
  · by_cases hlabel : label = edge.boneClass.label
    · rw [if_pos hlabel]
      apply d4LocalOwner_eq_edge_target
      rw [edge.class_spec.2]
      simpa [hlabel] using
        GoodBoneClass.localCellForLabel_shift edge.boneClass label
    · rw [if_neg hlabel]
      apply d4LocalOwner_eq_edge_source
      rw [edge.class_spec.2]
      simpa [hlabel] using
        GoodBoneClass.localCellForLabel_shift edge.boneClass label

theorem d4GoodEdge_rawCellForLabel {m : ℕ}
    (edge : D4LiteralDirectedEdge m) (label : MicroLabel) :
    d4RawCellOfLocal edge.placement (d4GoodEdgeLocalForLabel edge label) =
      ownerCell
        (if label = edge.boneClass.label then edge.target else edge.source)
        label := by
  have hcell := d4OwnerPairOfLocal_cell edge.placement
    (d4GoodEdgeLocalForLabel edge label)
  have hpair := d4GoodEdgeLocalForLabel_pair edge label
  rw [hpair.1, hpair.2] at hcell
  exact hcell.symm

theorem d4GoodEdge_covers_target_label {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (hpresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell edge.target edge.boneClass.label)) :
    D4PlacementCovers edge.placement
      ⟨ownerCell edge.target edge.boneClass.label, hpresent⟩ := by
  unfold D4PlacementCovers
  change ownerCell edge.target edge.boneClass.label ∈ edge.placement.cells
  rw [show ownerCell edge.target edge.boneClass.label =
      d4RawCellOfLocal edge.placement
        (d4GoodEdgeLocalForLabel edge edge.boneClass.label) by
    simpa using (d4GoodEdge_rawCellForLabel edge edge.boneClass.label).symm]
  simp only [D4LiteralPlacement.cells, d4PlacementCellList, List.mem_map]
  exact ⟨edge.boneClass.localCellForLabel edge.boneClass.label,
    by
      change edge.boneClass.localCellForLabel edge.boneClass.label ∈
        protoCells edge.placement.tile
      rw [edge.class_spec.1]
      exact GoodBoneClass.localCellForLabel_mem _ _,
    rfl⟩

theorem d4GoodEdge_target_present {m : ℕ}
    (edge : D4LiteralDirectedEdge m) :
    inBenzel (m + 4) (2 * m + 4)
      (ownerCell edge.target edge.boneClass.label) := by
  have hraw := d4GoodEdge_rawCellForLabel edge edge.boneClass.label
  rw [if_pos rfl] at hraw
  rw [← hraw]
  exact (d4CellOfLocal edge.placement
    (d4GoodEdgeLocalForLabel edge edge.boneClass.label)).2

theorem d4GoodEdge_covers_source_other {m : ℕ}
    (edge : D4LiteralDirectedEdge m) (label : MicroLabel)
    (hne : label ≠ edge.boneClass.label)
    (hpresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell edge.source label)) :
    D4PlacementCovers edge.placement
      ⟨ownerCell edge.source label, hpresent⟩ := by
  unfold D4PlacementCovers
  change ownerCell edge.source label ∈ edge.placement.cells
  rw [show ownerCell edge.source label =
      d4RawCellOfLocal edge.placement (d4GoodEdgeLocalForLabel edge label) by
    rw [d4GoodEdge_rawCellForLabel, if_neg hne]]
  simp only [D4LiteralPlacement.cells, d4PlacementCellList, List.mem_map]
  exact ⟨edge.boneClass.localCellForLabel label,
    by
      change edge.boneClass.localCellForLabel label ∈
        protoCells edge.placement.tile
      rw [edge.class_spec.1]
      exact GoodBoneClass.localCellForLabel_mem _ _,
    rfl⟩

theorem d4GoodEdge_source_other_present {m : ℕ}
    (edge : D4LiteralDirectedEdge m) (label : MicroLabel)
    (hne : label ≠ edge.boneClass.label) :
    inBenzel (m + 4) (2 * m + 4) (ownerCell edge.source label) := by
  have hraw := d4GoodEdge_rawCellForLabel edge label
  rw [if_neg hne] at hraw
  rw [← hraw]
  exact (d4CellOfLocal edge.placement
    (d4GoodEdgeLocalForLabel edge label)).2

end FiniteDefects
