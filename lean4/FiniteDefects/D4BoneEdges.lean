import FiniteDefects.D4FiniteDefect

/-! # Literal two-owner bones as labelled directed simplex edges -/

namespace FiniteDefects

def stepA : Cell := (2, -1)
def stepB : Cell := (-1, -1)
def stepC : Cell := (-1, 2)

def addCell (a b : Cell) : Cell := (a.1 + b.1, a.2 + b.2)

def allowedStep : MicroLabel → Cell → Prop
  | .zero, d => d = stepA ∨ d = stepC
  | .one, d => d = stepB ∨ d = stepC
  | .two, d => d = stepA ∨ d = stepB

theorem allowedStep_potential_increase
    (label : MicroLabel) (q r dq dr : ℤ)
    (h : allowedStep label (dq, dr)) :
    ownerPotential label (q + dq) (r + dr) =
      ownerPotential label q r + 1 := by
  rcases label with _ | _ | _ <;>
    simp only [allowedStep] at h <;>
    rcases h with h | h <;>
    simp only [stepA, stepB, stepC, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    simp [ownerPotential] <;>
    omega

def localOwnerDatum (baseResidue : Res3) (cell : LocalCell) :
    Cell × MicroLabel :=
  (ownerShift baseResidue cell, localLabel baseResidue cell)

def boneOwnerProfile (tile : ProtoTile) (baseResidue : Res3) :
    List (Cell × MicroLabel) :=
  (protoCells tile).map (localOwnerDatum baseResidue)

inductive GoodBoneClass
  | boneA0 | boneA2 | boneB0 | boneB1 | boneC0 | boneC2
  deriving DecidableEq, Repr

def GoodBoneClass.tile : GoodBoneClass → ProtoTile
  | .boneA0 | .boneA2 => .boneA
  | .boneB0 | .boneB1 => .boneB
  | .boneC0 | .boneC2 => .boneC

def GoodBoneClass.residue : GoodBoneClass → Res3
  | .boneA0 | .boneB0 | .boneC0 => .r0
  | .boneA2 | .boneC2 => .r2
  | .boneB1 => .r1

def GoodBoneClass.sourceShift : GoodBoneClass → Cell
  | .boneA0 | .boneB0 => (0, 0)
  | .boneA2 => (1, 0)
  | .boneB1 => (0, 1)
  | .boneC0 => (1, -2)
  | .boneC2 => (0, -1)

def GoodBoneClass.targetShift : GoodBoneClass → Cell
  | .boneA0 => stepA
  | .boneA2 => (0, -1)
  | .boneB0 => stepC
  | .boneB1 => (-1, 0)
  | .boneC0 => (0, 0)
  | .boneC2 => (2, -2)

def GoodBoneClass.label : GoodBoneClass → MicroLabel
  | .boneA0 | .boneA2 => .two
  | .boneB0 | .boneB1 => .one
  | .boneC0 | .boneC2 => .zero

def GoodBoneClass.step : GoodBoneClass → Cell
  | .boneA0 | .boneC2 => stepA
  | .boneA2 | .boneB1 => stepB
  | .boneB0 | .boneC0 => stepC

def D4IsPlacementClass {m : ℕ} (placement : D4LiteralPlacement m)
    (boneClass : GoodBoneClass) : Prop :=
  placement.tile = boneClass.tile ∧
    placementBaseResidue (m + 2) placement.base = boneClass.residue

theorem exists_unique_d4GoodBoneClass {m : ℕ}
    (placement : D4LiteralPlacement m)
    (hbone : placement.tile ≠ .stone)
    (htwo : ¬IsD4ThreeOwnerBone placement) :
    ∃! boneClass : GoodBoneClass,
      D4IsPlacementClass placement boneClass := by
  rcases htile : placement.tile with _ | _ | _ | _
  · exact (hbone htile).elim
  all_goals
    rcases hrho : placementBaseResidue (m + 2) placement.base with _ | _ | _
  all_goals
    simp [IsD4ThreeOwnerBone, htile, hrho] at htwo
  · refine ⟨.boneA0, ?_, ?_⟩
    · simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneA2, ?_, ?_⟩
    · simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneB0, ?_, ?_⟩
    · simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneB1, ?_, ?_⟩
    · simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneC0, ?_, ?_⟩
    · simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢
  · refine ⟨.boneC2, ?_, ?_⟩
    · simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho]
    · intro candidate hc
      rcases candidate <;> simp [D4IsPlacementClass, GoodBoneClass.tile,
        GoodBoneClass.residue, htile, hrho] at hc ⊢

theorem goodBoneClass_step_allowed (boneClass : GoodBoneClass) :
    allowedStep boneClass.label boneClass.step := by
  rcases boneClass <;>
    simp [GoodBoneClass.label, GoodBoneClass.step, allowedStep]

theorem goodBoneClass_target (boneClass : GoodBoneClass) :
    addCell boneClass.sourceShift boneClass.step = boneClass.targetShift := by
  rcases boneClass <;> decide

def GoodBoneClass.sourceWitnessLabel : GoodBoneClass → MicroLabel
  | .boneA0 | .boneA2 | .boneB0 | .boneB1 => .zero
  | .boneC0 | .boneC2 => .one

def GoodBoneClass.sourceWitnessCell : GoodBoneClass → LocalCell
  | .boneA0 | .boneB0 => c00
  | .boneA2 => c10
  | .boneB1 => c01
  | .boneC0 => c2m2
  | .boneC2 => c1m1

def GoodBoneClass.targetWitnessCell : GoodBoneClass → LocalCell
  | .boneA0 => c20
  | .boneA2 | .boneB1 | .boneC0 => c00
  | .boneB0 => c02
  | .boneC2 => c2m2

theorem sourceWitnessCell_mem (boneClass : GoodBoneClass) :
    boneClass.sourceWitnessCell ∈ protoCells boneClass.tile := by
  rcases boneClass <;> decide

theorem targetWitnessCell_mem (boneClass : GoodBoneClass) :
    boneClass.targetWitnessCell ∈ protoCells boneClass.tile := by
  rcases boneClass <;> decide

theorem sourceWitness_anchor (boneClass : GoodBoneClass) (base : Cell) :
    cellForOwnerAnchor
        (base.1 + boneClass.sourceShift.1,
          base.2 + boneClass.sourceShift.2)
        boneClass.sourceWitnessLabel =
      translateLocalCell base boneClass.sourceWitnessCell := by
  rcases boneClass <;>
    simp [GoodBoneClass.sourceShift, GoodBoneClass.sourceWitnessLabel,
      GoodBoneClass.sourceWitnessCell, cellForOwnerAnchor,
      translateLocalCell, c00, c10, c01, c1m1, c2m2]
  all_goals omega

theorem targetWitness_anchor (boneClass : GoodBoneClass) (base : Cell) :
    cellForOwnerAnchor
        (base.1 + boneClass.targetShift.1,
          base.2 + boneClass.targetShift.2)
        boneClass.label =
      translateLocalCell base boneClass.targetWitnessCell := by
  rcases boneClass <;>
    simp [GoodBoneClass.targetShift, GoodBoneClass.label,
      GoodBoneClass.targetWitnessCell, cellForOwnerAnchor,
      translateLocalCell, c00, c20, c02, c2m2, stepA, stepC]

theorem d4GoodBone_source_phase {m : ℕ}
    (placement : D4LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : D4IsPlacementClass placement boneClass) :
    IsOwnerPhase (m + 2)
      (placement.base.1 + boneClass.sourceShift.1,
        placement.base.2 + boneClass.sourceShift.2) := by
  have hbase := placementBaseResidue_spec (m + 2) placement.base
  unfold BaseHasResidue at hbase
  rw [hclass.2] at hbase
  rcases boneClass <;>
    simp only [GoodBoneClass.residue, Res3.value,
      GoodBoneClass.sourceShift] at hbase ⊢ <;>
    apply shifted_anchor_is_phase hbase <;> norm_num

theorem d4GoodBone_target_phase {m : ℕ}
    (placement : D4LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : D4IsPlacementClass placement boneClass) :
    IsOwnerPhase (m + 2)
      (placement.base.1 + boneClass.targetShift.1,
        placement.base.2 + boneClass.targetShift.2) := by
  have hbase := placementBaseResidue_spec (m + 2) placement.base
  unfold BaseHasResidue at hbase
  rw [hclass.2] at hbase
  rcases boneClass <;>
    simp only [GoodBoneClass.residue, Res3.value,
      GoodBoneClass.targetShift, stepA, stepC] at hbase ⊢ <;>
    apply shifted_anchor_is_phase hbase <;> norm_num

theorem d4SourceWitness_mem {m : ℕ}
    (placement : D4LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : D4IsPlacementClass placement boneClass) :
    inBenzel (m + 4) (2 * m + 4)
      (cellForOwnerAnchor
        (placement.base.1 + boneClass.sourceShift.1,
          placement.base.2 + boneClass.sourceShift.2)
        boneClass.sourceWitnessLabel) := by
  rw [sourceWitness_anchor]
  apply placement.2
  simp only [D4LiteralPlacement.cells, d4PlacementCellList, List.mem_map]
  exact ⟨boneClass.sourceWitnessCell,
    by
      change boneClass.sourceWitnessCell ∈ protoCells placement.tile
      rw [hclass.1]
      exact sourceWitnessCell_mem boneClass,
    rfl⟩

theorem d4TargetWitness_mem {m : ℕ}
    (placement : D4LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : D4IsPlacementClass placement boneClass) :
    inBenzel (m + 4) (2 * m + 4)
      (cellForOwnerAnchor
        (placement.base.1 + boneClass.targetShift.1,
          placement.base.2 + boneClass.targetShift.2)
        boneClass.label) := by
  rw [targetWitness_anchor]
  apply placement.2
  simp only [D4LiteralPlacement.cells, d4PlacementCellList, List.mem_map]
  exact ⟨boneClass.targetWitnessCell,
    by
      change boneClass.targetWitnessCell ∈ protoCells placement.tile
      rw [hclass.1]
      exact targetWitnessCell_mem boneClass,
    rfl⟩

theorem exists_d4GoodBone_source {m : ℕ}
    (placement : D4LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : D4IsPlacementClass placement boneClass) :
    ∃ p : SimplexPoint (m + 2),
      ownerQ p = placement.base.1 + boneClass.sourceShift.1 ∧
      ownerR p = placement.base.2 + boneClass.sourceShift.2 := by
  exact phase_anchor_has_simplex (m + 2) (2 * m + 4)
    (placement.base.1 + boneClass.sourceShift.1,
      placement.base.2 + boneClass.sourceShift.2)
    boneClass.sourceWitnessLabel
    (d4GoodBone_source_phase placement boneClass hclass)
    (d4SourceWitness_mem placement boneClass hclass)

theorem exists_d4GoodBone_target {m : ℕ}
    (placement : D4LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : D4IsPlacementClass placement boneClass) :
    ∃ p : SimplexPoint (m + 2),
      ownerQ p = placement.base.1 + boneClass.targetShift.1 ∧
      ownerR p = placement.base.2 + boneClass.targetShift.2 := by
  exact phase_anchor_has_simplex (m + 2) (2 * m + 4)
    (placement.base.1 + boneClass.targetShift.1,
      placement.base.2 + boneClass.targetShift.2)
    boneClass.label
    (d4GoodBone_target_phase placement boneClass hclass)
    (d4TargetWitness_mem placement boneClass hclass)

structure D4LiteralDirectedEdge (m : ℕ) where
  placement : D4LiteralPlacement m
  boneClass : GoodBoneClass
  class_spec : D4IsPlacementClass placement boneClass
  source : SimplexPoint (m + 2)
  target : SimplexPoint (m + 2)
  source_anchor :
    ownerQ source = placement.base.1 + boneClass.sourceShift.1 ∧
    ownerR source = placement.base.2 + boneClass.sourceShift.2
  target_anchor :
    ownerQ target = placement.base.1 + boneClass.targetShift.1 ∧
    ownerR target = placement.base.2 + boneClass.targetShift.2

noncomputable def d4LiteralDirectedEdgeOfPlacement {m : ℕ}
    (placement : D4LiteralPlacement m)
    (hbone : placement.tile ≠ .stone)
    (htwo : ¬IsD4ThreeOwnerBone placement) : D4LiteralDirectedEdge m := by
  let boneClass := (exists_unique_d4GoodBoneClass placement hbone htwo).choose
  have hclass : D4IsPlacementClass placement boneClass :=
    (exists_unique_d4GoodBoneClass placement hbone htwo).choose_spec.1
  let source := (exists_d4GoodBone_source placement boneClass hclass).choose
  have hsource :=
    (exists_d4GoodBone_source placement boneClass hclass).choose_spec
  let target := (exists_d4GoodBone_target placement boneClass hclass).choose
  have htarget :=
    (exists_d4GoodBone_target placement boneClass hclass).choose_spec
  exact
    { placement := placement
      boneClass := boneClass
      class_spec := hclass
      source := source
      target := target
      source_anchor := hsource
      target_anchor := htarget }

theorem d4LiteralDirectedEdge_anchor_step {m : ℕ}
    (edge : D4LiteralDirectedEdge m) :
    addCell (ownerQ edge.source, ownerR edge.source) edge.boneClass.step =
      (ownerQ edge.target, ownerR edge.target) := by
  rw [edge.source_anchor.1, edge.source_anchor.2,
    edge.target_anchor.1, edge.target_anchor.2]
  have htarget := goodBoneClass_target edge.boneClass
  apply Prod.ext
  · have h := congrArg Prod.fst htarget
    simp [addCell] at h ⊢
    omega
  · have h := congrArg Prod.snd htarget
    simp [addCell] at h ⊢
    omega

theorem stepA_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hstep : addCell (ownerQ p, ownerR p) stepA =
      (ownerQ q, ownerR q)) :
    q.u + 1 = p.u ∧ q.v = p.v ∧ q.w = p.w + 1 := by
  have hq := congrArg Prod.fst hstep
  have hr := congrArg Prod.snd hstep
  have hu := recover_u_numerator p
  have hu' := recover_u_numerator q
  have hv := recover_v_numerator p
  have hv' := recover_v_numerator q
  have hw := recover_w_numerator p
  have hw' := recover_w_numerator q
  simp [addCell, stepA] at hq hr
  constructor <;> omega

theorem stepB_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hstep : addCell (ownerQ p, ownerR p) stepB =
      (ownerQ q, ownerR q)) :
    q.u = p.u ∧ q.v = p.v + 1 ∧ q.w + 1 = p.w := by
  have hq := congrArg Prod.fst hstep
  have hr := congrArg Prod.snd hstep
  have hu := recover_u_numerator p
  have hu' := recover_u_numerator q
  have hv := recover_v_numerator p
  have hv' := recover_v_numerator q
  have hw := recover_w_numerator p
  have hw' := recover_w_numerator q
  simp [addCell, stepB] at hq hr
  constructor <;> omega

theorem stepC_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hstep : addCell (ownerQ p, ownerR p) stepC =
      (ownerQ q, ownerR q)) :
    q.u = p.u + 1 ∧ q.v + 1 = p.v ∧ q.w = p.w := by
  have hq := congrArg Prod.fst hstep
  have hr := congrArg Prod.snd hstep
  have hu := recover_u_numerator p
  have hu' := recover_u_numerator q
  have hv := recover_v_numerator p
  have hv' := recover_v_numerator q
  have hw := recover_w_numerator p
  have hw' := recover_w_numerator q
  simp [addCell, stepC] at hq hr
  constructor <;> omega

theorem d4LiteralDirectedEdge_simplex_step {m : ℕ}
    (edge : D4LiteralDirectedEdge m) :
    (edge.boneClass.step = stepA ∧
        edge.target.u + 1 = edge.source.u ∧
        edge.target.v = edge.source.v ∧
        edge.target.w = edge.source.w + 1) ∨
    (edge.boneClass.step = stepB ∧
        edge.target.u = edge.source.u ∧
        edge.target.v = edge.source.v + 1 ∧
        edge.target.w + 1 = edge.source.w) ∨
    (edge.boneClass.step = stepC ∧
        edge.target.u = edge.source.u + 1 ∧
        edge.target.v + 1 = edge.source.v ∧
        edge.target.w = edge.source.w) := by
  have hanchor := d4LiteralDirectedEdge_anchor_step edge
  generalize hc : edge.boneClass = boneClass at hanchor ⊢
  cases boneClass <;>
    simp only [GoodBoneClass.step] at hanchor
  · exact Or.inl ⟨rfl, stepA_simplex_coordinates edge.source edge.target hanchor⟩
  · exact Or.inr (Or.inl
      ⟨rfl, stepB_simplex_coordinates edge.source edge.target hanchor⟩)
  · exact Or.inr (Or.inr
      ⟨rfl, stepC_simplex_coordinates edge.source edge.target hanchor⟩)
  · exact Or.inr (Or.inl
      ⟨rfl, stepB_simplex_coordinates edge.source edge.target hanchor⟩)
  · exact Or.inr (Or.inr
      ⟨rfl, stepC_simplex_coordinates edge.source edge.target hanchor⟩)
  · exact Or.inl ⟨rfl, stepA_simplex_coordinates edge.source edge.target hanchor⟩

end FiniteDefects
