import BenzelProblem6Kernel.LiteralDirectedEdge

/-!
# Literal cell coverage of a directed good-bone edge
-/

namespace BenzelProblem6Kernel

theorem exists_source_label_witness (boneClass : GoodBoneClass)
    (base : Cell) (label : MicroLabel) (hne : label ≠ boneClass.label) :
    ∃ localCell ∈ protoCells boneClass.tile,
      cellForOwnerAnchor
          (base.1 + boneClass.sourceShift.1,
            base.2 + boneClass.sourceShift.2) label =
        translateLocalCell base localCell := by
  rcases boneClass <;> rcases label <;>
    simp [GoodBoneClass.label, GoodBoneClass.tile, GoodBoneClass.sourceShift,
      protoCells, cellForOwnerAnchor, translateLocalCell,
      c00, c10, c20, c01, c02, c1m1, c2m2] at hne ⊢
  all_goals omega

theorem literalDirectedEdge_source_cell_eq {m : ℕ}
    (edge : LiteralDirectedEdge m) (label : MicroLabel)
    (hne : label ≠ edge.boneClass.label) :
    ∃ localCell ∈ protoCells edge.placement.tile,
      ownerCell edge.source label =
        translateLocalCell edge.placement.base localCell := by
  obtain ⟨localCell, hlocal, heq⟩ :=
    exists_source_label_witness edge.boneClass edge.placement.base label hne
  refine ⟨localCell, ?_, ?_⟩
  · rw [edge.class_spec.1]
    exact hlocal
  · rw [ownerCell_eq_cellForOwnerAnchor,
      edge.source_anchor.1, edge.source_anchor.2]
    exact heq

theorem literalDirectedEdge_target_cell_eq {m : ℕ}
    (edge : LiteralDirectedEdge m) :
    ∃ localCell ∈ protoCells edge.placement.tile,
      ownerCell edge.target edge.boneClass.label =
        translateLocalCell edge.placement.base localCell := by
  refine ⟨edge.boneClass.targetWitnessCell, ?_, ?_⟩
  · rw [edge.class_spec.1]
    exact targetWitnessCell_mem edge.boneClass
  · rw [ownerCell_eq_cellForOwnerAnchor,
      edge.target_anchor.1, edge.target_anchor.2]
    exact targetWitness_anchor edge.boneClass edge.placement.base

theorem literalDirectedEdge_source_cell_mem {m : ℕ}
    (edge : LiteralDirectedEdge m) (label : MicroLabel)
    (hne : label ≠ edge.boneClass.label) :
    inPeripheralBenzel (m + 5) (ownerCell edge.source label) := by
  obtain ⟨localCell, hlocal, heq⟩ :=
    literalDirectedEdge_source_cell_eq edge label hne
  rw [heq]
  apply edge.placement.2
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
  exact ⟨localCell, hlocal, rfl⟩

theorem literalDirectedEdge_target_cell_mem {m : ℕ}
    (edge : LiteralDirectedEdge m) :
    inPeripheralBenzel (m + 5)
      (ownerCell edge.target edge.boneClass.label) := by
  obtain ⟨localCell, hlocal, heq⟩ := literalDirectedEdge_target_cell_eq edge
  rw [heq]
  apply edge.placement.2
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
  exact ⟨localCell, hlocal, rfl⟩

theorem literalDirectedEdge_covers_source_cell {m : ℕ}
    (edge : LiteralDirectedEdge m) (label : MicroLabel)
    (hne : label ≠ edge.boneClass.label) :
    PlacementCovers edge.placement
      (⟨ownerCell edge.source label,
        literalDirectedEdge_source_cell_mem edge label hne⟩ : BenzelCell (m + 5)) := by
  obtain ⟨localCell, hlocal, heq⟩ :=
    literalDirectedEdge_source_cell_eq edge label hne
  change ownerCell edge.source label ∈ edge.placement.cells
  rw [heq]
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
  exact ⟨localCell, hlocal, rfl⟩

theorem literalDirectedEdge_covers_target_cell {m : ℕ}
    (edge : LiteralDirectedEdge m) :
    PlacementCovers edge.placement
      (⟨ownerCell edge.target edge.boneClass.label,
        literalDirectedEdge_target_cell_mem edge⟩ : BenzelCell (m + 5)) := by
  obtain ⟨localCell, hlocal, heq⟩ := literalDirectedEdge_target_cell_eq edge
  change ownerCell edge.target edge.boneClass.label ∈ edge.placement.cells
  rw [heq]
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
  exact ⟨localCell, hlocal, rfl⟩

end BenzelProblem6Kernel
