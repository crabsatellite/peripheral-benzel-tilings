import BenzelProblem6Kernel.ActiveOwnerSources
import BenzelProblem6Kernel.GoodBoneCellRoles

/-!
# Role of the unique covering placement at one owner label
-/

namespace BenzelProblem6Kernel

theorem directedEdgeOfBoneMember_mem
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ bonePlacementFinset tiling}) :
    directedEdgeOfBoneMember hstone tiling placement ∈
      literalDirectedEdges hstone tiling := by
  classical
  simp only [literalDirectedEdges, Finset.mem_map, Finset.mem_attach]
  exact ⟨placement, by simp, rfl⟩

theorem edge_local_source_cell_eq {m : ℕ} (edge : LiteralDirectedEdge m)
    (localCell : LocalCell) (hshift :
      (localOwnerDatum edge.boneClass.residue localCell).1 =
        edge.boneClass.sourceShift) :
    ownerCell edge.source
        (localOwnerDatum edge.boneClass.residue localCell).2 =
      translateLocalCell edge.placement.base localCell := by
  rw [ownerCell_eq_cellForOwnerAnchor,
    edge.source_anchor.1, edge.source_anchor.2]
  have hanchor := ownerAnchorForCell_translate_eq edge.placement.base
    edge.boneClass.residue localCell
  change ownerShift edge.boneClass.residue localCell =
    edge.boneClass.sourceShift at hshift
  rw [hshift] at hanchor
  have hanchor' :
      ownerAnchorForCell (translateLocalCell edge.placement.base localCell)
          (localOwnerDatum edge.boneClass.residue localCell).2 =
        (edge.placement.base.1 + edge.boneClass.sourceShift.1,
          edge.placement.base.2 + edge.boneClass.sourceShift.2) := by
    simpa [localOwnerDatum] using hanchor
  rw [← hanchor']
  exact cell_anchor_roundtrip _ _

theorem edge_local_target_cell_eq {m : ℕ} (edge : LiteralDirectedEdge m)
    (localCell : LocalCell) (hshift :
      (localOwnerDatum edge.boneClass.residue localCell).1 =
        edge.boneClass.targetShift) :
    ownerCell edge.target
        (localOwnerDatum edge.boneClass.residue localCell).2 =
      translateLocalCell edge.placement.base localCell := by
  rw [ownerCell_eq_cellForOwnerAnchor,
    edge.target_anchor.1, edge.target_anchor.2]
  have hanchor := ownerAnchorForCell_translate_eq edge.placement.base
    edge.boneClass.residue localCell
  change ownerShift edge.boneClass.residue localCell =
    edge.boneClass.targetShift at hshift
  rw [hshift] at hanchor
  have hanchor' :
      ownerAnchorForCell (translateLocalCell edge.placement.base localCell)
          (localOwnerDatum edge.boneClass.residue localCell).2 =
        (edge.placement.base.1 + edge.boneClass.targetShift.1,
          edge.placement.base.2 + edge.boneClass.targetShift.2) := by
    simpa [localOwnerDatum] using hanchor
  rw [← hanchor']
  exact cell_anchor_roundtrip _ _

theorem covering_bone_edge_role
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (p : SimplexPoint (m + 3)) (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5) (ownerCell p label))
    (placement : LiteralPlacement m)
    (hplacement : placement ∈ tiling.1)
    (hbone : placement.tile ≠ .stone)
    (hcover : PlacementCovers placement
      (⟨ownerCell p label, hmem⟩ : BenzelCell (m + 5))) :
    ∃ edge ∈ literalDirectedEdges hstone tiling,
      edge.placement = placement ∧
      ((edge.source = p ∧ edge.boneClass.label ≠ label) ∨
        (edge.target = p ∧ edge.boneClass.label = label)) := by
  classical
  let member : {q // q ∈ bonePlacementFinset tiling} :=
    ⟨placement, by simp [bonePlacementFinset, hplacement, hbone]⟩
  let edge := directedEdgeOfBoneMember hstone tiling member
  have hedge : edge ∈ literalDirectedEdges hstone tiling :=
    directedEdgeOfBoneMember_mem hstone tiling member
  have hedgePlacement : edge.placement = placement := rfl
  have hcoverRaw : ownerCell p label ∈ placement.cells := hcover
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map] at hcoverRaw
  obtain ⟨localCell, hlocalPlacement, hlocalEq⟩ := hcoverRaw
  have hlocalClass : localCell ∈ protoCells edge.boneClass.tile := by
    change localCell ∈ protoCells placement.tile at hlocalPlacement
    rw [← hedgePlacement, edge.class_spec.1] at hlocalPlacement
    exact hlocalPlacement
  have hrole := goodBoneClass_cell_role edge.boneClass localCell hlocalClass
  refine ⟨edge, hedge, hedgePlacement, ?_⟩
  rcases hrole with hsource | htarget
  · left
    have hedgeCell := edge_local_source_cell_eq edge localCell hsource.1
    rw [hedgePlacement] at hedgeCell
    have hsameCell : ownerCell edge.source
        (localOwnerDatum edge.boneClass.residue localCell).2 =
          ownerCell p label := by
      exact hedgeCell.trans hlocalEq
    obtain ⟨howner, hlabel⟩ := owner_representation_unique (n := m + 5)
      (ownerCell p label) edge.source p
      (localOwnerDatum edge.boneClass.residue localCell).2 label
      hsameCell rfl
    have hne : label ≠ edge.boneClass.label := by
      simpa [hlabel] using hsource.2
    exact ⟨howner, hne.symm⟩
  · right
    have hedgeCell := edge_local_target_cell_eq edge localCell htarget.1
    rw [hedgePlacement] at hedgeCell
    have hsameCell : ownerCell edge.target
        (localOwnerDatum edge.boneClass.residue localCell).2 =
          ownerCell p label := by
      exact hedgeCell.trans hlocalEq
    obtain ⟨howner, hlabel⟩ := owner_representation_unique (n := m + 5)
      (ownerCell p label) edge.target p
      (localOwnerDatum edge.boneClass.residue localCell).2 label
      hsameCell rfl
    exact ⟨howner, htarget.2.symm.trans hlabel⟩

end BenzelProblem6Kernel
