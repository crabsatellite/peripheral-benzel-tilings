import FiniteDefects.D4ArmDecodePath

/-! # The literal arm decoder is inverse to the ballot-word encoder -/

namespace FiniteDefects

@[simp] theorem d4GoodBoneClassOfReverseMove_inverse
    (boneClass : GoodBoneClass) :
    d4GoodBoneClassOfReverseMove boneClass.label
      (d4ReverseMove boneClass) = boneClass := by
  rcases boneClass <;> rfl

theorem d4LiteralDirectedEdge_base_eq_reverse {m : ℕ}
    (edge : D4LiteralDirectedEdge m) :
    edge.placement.base = reverseBoneBase edge.source edge.boneClass := by
  apply Prod.ext
  · have h := edge.source_anchor.1
    simp only [reverseBoneBase]
    omega
  · have h := edge.source_anchor.2
    simp only [reverseBoneBase]
    omega

theorem d4LiteralPlacement_ext_tile_base {m : ℕ}
    (left right : D4LiteralPlacement m)
    (htile : left.tile = right.tile) (hbase : left.base = right.base) :
    left = right := by
  apply Subtype.ext
  apply Prod.ext
  · exact htile
  · apply Subtype.ext
    exact hbase

theorem D4LiteralDirectedEdge.ext_of_source_class {m : ℕ}
    (left right : D4LiteralDirectedEdge m)
    (hsource : left.source = right.source)
    (hclass : left.boneClass = right.boneClass) : left = right := by
  apply D4LiteralDirectedEdge.ext_of_placement
  apply d4LiteralPlacement_ext_tile_base
  · rw [left.class_spec.1, right.class_spec.1, hclass]
  · rw [d4LiteralDirectedEdge_base_eq_reverse,
      d4LiteralDirectedEdge_base_eq_reverse, hsource, hclass]

theorem simplex_source_unique_of_addCell {t : ℕ}
    (left right : SimplexPoint t) (step targetAnchor : Cell)
    (hleft : addCell (ownerQ left, ownerR left) step = targetAnchor)
    (hright : addCell (ownerQ right, ownerR right) step = targetAnchor) :
    left = right := by
  apply simplex_eq_of_owner_anchor
  · have hl := congrArg Prod.fst hleft
    have hr := congrArg Prod.fst hright
    simp only [addCell] at hl hr
    omega
  · have hl := congrArg Prod.snd hleft
    have hr := congrArg Prod.snd hright
    simp only [addCell] at hl hr
    omega

theorem d4DecodeArmEdgesAux_eq_of_path {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (terminal : SimplexPoint (m + 2))
    (edges : List (D4LiteralDirectedEdge m))
    (hpath : IsD4AbstractReversePath label terminal core edges)
    (pre : List BallotMove)
    (hword : pre ++ d4ArmWord edges = data.word)
    (hterminal : d4ArmPoint label core data pre (by
      rw [← hword]
      exact List.prefix_append pre (d4ArmWord edges)) = terminal) :
    d4DecodeArmEdgesAux label core hroom data pre
      (d4ArmWord edges) hword = edges := by
  induction edges generalizing pre terminal with
  | nil => simp [d4DecodeArmEdgesAux, d4ArmWord]
  | cons edge rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      let move := d4ReverseMove edge.boneClass
      have hlabel : edge.boneClass.label = label := hpath.2.1
      have hwordShape : d4ArmWord (edge :: rest) =
          move :: d4ArmWord rest := by rfl
      have hwordNext : (pre ++ [move]) ++ d4ArmWord rest = data.word := by
        rw [← hword]
        simp [hwordShape, List.append_assoc, move]
      have hp : pre ++ [move] <+: data.word := by
        rw [← hwordNext]
        exact List.prefix_append (pre ++ [move]) (d4ArmWord rest)
      let decoded := d4ArmEdge label core hroom data pre move hp
      have hclass : decoded.boneClass = edge.boneClass := by
        rw [d4ArmEdge_boneClass]
        rw [← hlabel]
        exact d4GoodBoneClassOfReverseMove_inverse edge.boneClass
      have htarget : decoded.target = edge.target := by
        rw [d4ArmEdge_target]
        exact hterminal.trans hpath.1.symm
      have hdecodedStep := d4LiteralDirectedEdge_anchor_step decoded
      have hedgeStep := d4LiteralDirectedEdge_anchor_step edge
      rw [hclass, htarget] at hdecodedStep
      have hsource : decoded.source = edge.source :=
        simplex_source_unique_of_addCell decoded.source edge.source
          edge.boneClass.step (ownerQ edge.target, ownerR edge.target)
          hdecodedStep hedgeStep
      have hedge : decoded = edge :=
        D4LiteralDirectedEdge.ext_of_source_class decoded edge hsource hclass
      have hsourcePoint :
          d4ArmPoint label core data (pre ++ [move]) hp = edge.source := by
        rw [← hsource]
        exact (d4ArmEdge_source label core hroom data pre move hp).symm
      have htail := ih edge.source hpath.2.2
        (pre ++ [move]) hwordNext hsourcePoint
      calc
        d4DecodeArmEdgesAux label core hroom data pre
            (d4ArmWord (edge :: rest)) hword =
            decoded :: d4DecodeArmEdgesAux label core hroom data
              (pre ++ [move]) (d4ArmWord rest) hwordNext := by
                simp [d4ArmWord, d4DecodeArmEdgesAux, move, decoded]
        _ = edge :: rest := congrArg₂ List.cons hedge htail

@[simp] theorem d4ConcreteToArmPath_encode {m : ℕ}
    (label : MicroLabel) (core : SimplexPoint (m + 2))
    (hroom : d4ArmRoom label core) (path : D4ArmPath m label core) :
    d4ConcreteToArmPath label core hroom
      (d4ArmPathToConcreteExact label core path) = path := by
  apply Subtype.ext
  exact d4DecodeArmEdgesAux_eq_of_path label core hroom
    (d4ArmPathToConcreteExact label core path)
    (d4BoundaryOwner m label) path.1 path.2 [] (by simp) (by
      rw [d4ArmPoint_nil])

noncomputable def d4ArmPathEquivConcrete {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core) :
    D4ArmPath m label core ≃
      ConcreteBallotWord (d4ArmMajority label core)
        (d4ArmMinority label core) where
  toFun := d4ArmPathToConcreteExact label core
  invFun := d4ConcreteToArmPath label core hroom
  left_inv := d4ConcreteToArmPath_encode label core hroom
  right_inv := d4ArmPathToConcrete_decode label core hroom

end FiniteDefects
