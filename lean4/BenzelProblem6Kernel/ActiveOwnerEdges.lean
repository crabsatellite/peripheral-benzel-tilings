import BenzelProblem6Kernel.ActiveOwnerCount
import BenzelProblem6Kernel.LiteralEdgeCoverage

/-!
# Every literal directed edge is incident only with active owners
-/

namespace BenzelProblem6Kernel

theorem edge_source_not_stone_owner
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    edge.source ∉ stoneOwnerFinset hstone tiling := by
  intro hsource
  simp only [stoneOwnerFinset, Finset.mem_map, Finset.mem_attach] at hsource
  obtain ⟨stonePlacement, _, howner⟩ := hsource
  obtain ⟨label, hlabel, _⟩ :=
    exists_microLabel_ne_two edge.boneClass.label edge.boneClass.label
  let cell : BenzelCell (m + 5) :=
    ⟨ownerCell edge.source label,
      literalDirectedEdge_source_cell_mem edge label hlabel⟩
  have hedgeCover : PlacementCovers edge.placement cell :=
    literalDirectedEdge_covers_source_cell edge label hlabel
  have hstoneCover : PlacementCovers stonePlacement.1 cell := by
    have hc := stone_placement_covers_owner_label hstone tiling stonePlacement label
    have hcell :
        (⟨ownerCell (stoneOwner hstone tiling stonePlacement) label, by
          rw [ownerCell_eq_cellForOwnerAnchor,
            (stoneOwner_anchor hstone tiling stonePlacement).1,
            (stoneOwner_anchor hstone tiling stonePlacement).2,
            stoneLabelLocalCell_anchor]
          apply stonePlacement.1.2
          simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
          have hp := stonePlacement.2
          simp only [stonePlacementFinset, Finset.mem_filter] at hp
          refine ⟨stoneLabelLocalCell label, ?_, rfl⟩
          change stoneLabelLocalCell label ∈ protoCells stonePlacement.1.tile
          rw [hp.2]
          exact stoneLabelLocalCell_mem label⟩ : BenzelCell (m + 5)) = cell := by
      apply Subtype.ext
      change ownerCell (stoneOwner hstone tiling stonePlacement) label =
        ownerCell edge.source label
      simpa [stoneOwnerEmbedding] using
        congrArg (fun p => ownerCell p label) howner
    simpa [hcell] using hc
  have hedgeMem := (mem_literalDirectedEdges_placement hstone tiling edge hedge).1
  have hstoneMem := stonePlacement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hstoneMem
  obtain ⟨placement, _, hunique⟩ := tiling.2 cell
  have heq := (hunique edge.placement ⟨hedgeMem, hedgeCover⟩).trans
    (hunique stonePlacement.1 ⟨hstoneMem.1, hstoneCover⟩).symm
  have hedgeBone := (mem_literalDirectedEdges_placement hstone tiling edge hedge).2
  apply hedgeBone
  rw [heq]
  exact hstoneMem.2

theorem edge_target_not_stone_owner
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    edge.target ∉ stoneOwnerFinset hstone tiling := by
  intro htarget
  simp only [stoneOwnerFinset, Finset.mem_map, Finset.mem_attach] at htarget
  obtain ⟨stonePlacement, _, howner⟩ := htarget
  let label := edge.boneClass.label
  let cell : BenzelCell (m + 5) :=
    ⟨ownerCell edge.target label, literalDirectedEdge_target_cell_mem edge⟩
  have hedgeCover : PlacementCovers edge.placement cell :=
    literalDirectedEdge_covers_target_cell edge
  have hstoneCover : PlacementCovers stonePlacement.1 cell := by
    have hc := stone_placement_covers_owner_label hstone tiling stonePlacement label
    have hcell :
        (⟨ownerCell (stoneOwner hstone tiling stonePlacement) label, by
          rw [ownerCell_eq_cellForOwnerAnchor,
            (stoneOwner_anchor hstone tiling stonePlacement).1,
            (stoneOwner_anchor hstone tiling stonePlacement).2,
            stoneLabelLocalCell_anchor]
          apply stonePlacement.1.2
          simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
          have hp := stonePlacement.2
          simp only [stonePlacementFinset, Finset.mem_filter] at hp
          refine ⟨stoneLabelLocalCell label, ?_, rfl⟩
          change stoneLabelLocalCell label ∈ protoCells stonePlacement.1.tile
          rw [hp.2]
          exact stoneLabelLocalCell_mem label⟩ : BenzelCell (m + 5)) = cell := by
      apply Subtype.ext
      change ownerCell (stoneOwner hstone tiling stonePlacement) label =
        ownerCell edge.target label
      simpa [stoneOwnerEmbedding] using
        congrArg (fun p => ownerCell p label) howner
    simpa [hcell] using hc
  have hedgeMem := (mem_literalDirectedEdges_placement hstone tiling edge hedge).1
  have hstoneMem := stonePlacement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hstoneMem
  obtain ⟨placement, _, hunique⟩ := tiling.2 cell
  have heq := (hunique edge.placement ⟨hedgeMem, hedgeCover⟩).trans
    (hunique stonePlacement.1 ⟨hstoneMem.1, hstoneCover⟩).symm
  have hedgeBone := (mem_literalDirectedEdges_placement hstone tiling edge hedge).2
  apply hedgeBone
  rw [heq]
  exact hstoneMem.2

theorem edge_source_mem_active
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    edge.source ∈ activeOwnerFinset hstone tiling := by
  simp [activeOwnerFinset, edge_source_not_stone_owner hstone tiling edge hedge]

theorem edge_target_mem_active
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    edge.target ∈ activeOwnerFinset hstone tiling := by
  simp [activeOwnerFinset, edge_target_not_stone_owner hstone tiling edge hedge]

end BenzelProblem6Kernel
