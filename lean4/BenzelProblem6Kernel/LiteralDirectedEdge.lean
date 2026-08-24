import BenzelProblem6Kernel.GoodBoneOwnerWitness

/-!
# Literal good bones as labelled directed simplex edges
-/

namespace BenzelProblem6Kernel

structure LiteralDirectedEdge (m : ℕ) where
  placement : LiteralPlacement m
  boneClass : GoodBoneClass
  class_spec : IsPlacementClass placement boneClass
  source : SimplexPoint (m + 3)
  target : SimplexPoint (m + 3)
  source_anchor :
    ownerQ source = placement.base.1 + boneClass.sourceShift.1 ∧
    ownerR source = placement.base.2 + boneClass.sourceShift.2
  target_anchor :
    ownerQ target = placement.base.1 + boneClass.targetShift.1 ∧
    ownerR target = placement.base.2 + boneClass.targetShift.2

noncomputable def literalDirectedEdgeOfPlacement {m : ℕ}
    (placement : LiteralPlacement m)
    (hbone : placement.tile ≠ .stone)
    (htwo : ¬IsThreeOwnerBone placement) : LiteralDirectedEdge m := by
  let boneClass := (exists_unique_goodBoneClass placement hbone htwo).choose
  have hclass : IsPlacementClass placement boneClass :=
    (exists_unique_goodBoneClass placement hbone htwo).choose_spec.1
  let source := (exists_goodBone_source_simplex placement boneClass hclass).choose
  have hsource :=
    (exists_goodBone_source_simplex placement boneClass hclass).choose_spec
  let target := (exists_goodBone_target_simplex placement boneClass hclass).choose
  have htarget :=
    (exists_goodBone_target_simplex placement boneClass hclass).choose_spec
  exact
    { placement := placement
      boneClass := boneClass
      class_spec := hclass
      source := source
      target := target
      source_anchor := hsource
      target_anchor := htarget }

theorem literalDirectedEdge_anchor_step {m : ℕ} (edge : LiteralDirectedEdge m) :
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

theorem literalDirectedEdge_allowed {m : ℕ} (edge : LiteralDirectedEdge m) :
    allowedStep edge.boneClass.label edge.boneClass.step :=
  goodBoneClass_step_allowed edge.boneClass

theorem literalDirectedEdge_simplex_step {m : ℕ} (edge : LiteralDirectedEdge m) :
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
  have hanchor := literalDirectedEdge_anchor_step edge
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

theorem literalDirectedEdge_source_ne_target {m : ℕ}
    (edge : LiteralDirectedEdge m) : edge.source ≠ edge.target := by
  intro h
  rcases literalDirectedEdge_simplex_step edge with hA | hB | hC
  · rw [h] at hA
    omega
  · rw [h] at hB
    omega
  · rw [h] at hC
    omega

end BenzelProblem6Kernel
