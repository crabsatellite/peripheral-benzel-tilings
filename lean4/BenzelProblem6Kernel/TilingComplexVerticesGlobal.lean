import BenzelProblem6Kernel.TilingCellVertexUnion
import BenzelProblem6Kernel.TilingBoundaryNodup

/-! # Global vertex decomposition into boundary vertices and stone centers -/

namespace BenzelProblem6Kernel

noncomputable def tilingBoundaryVertexFinset {m : ℕ}
    (tiling : LiteralTiling m) : Finset HexVertex :=
  tiling.1.biUnion placementBoundaryVertexFinset

noncomputable def tilingStoneCenterFinset {m : ℕ}
    (tiling : LiteralTiling m) : Finset HexVertex :=
  (tiling.1.filter fun placement => placement.tile = .stone).image
    (fun placement => upHexVertex placement.base)

theorem tilingCellVertexFinset_decomposition {m : ℕ}
    (tiling : LiteralTiling m) :
    tilingCellVertexFinset tiling =
      tilingBoundaryVertexFinset tiling ∪
        tilingStoneCenterFinset tiling := by
  ext vertex
  simp only [tilingCellVertexFinset, tilingBoundaryVertexFinset,
    tilingStoneCenterFinset, Finset.mem_biUnion,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨placement, hplacement, hvertex⟩
    rw [placement_vertex_decomposition, Finset.mem_union] at hvertex
    rcases hvertex with hboundary | hcenter
    · exact Or.inl ⟨placement, hplacement, hboundary⟩
    · by_cases hstone : placement.tile = .stone
      · simp [hstone] at hcenter
        exact Or.inr ⟨placement, ⟨hplacement, hstone⟩, hcenter.symm⟩
      · simp [hstone] at hcenter
  · rintro (⟨placement, hplacement, hboundary⟩ |
      ⟨placement, ⟨hplacement, hstone⟩, hcenter⟩)
    · refine ⟨placement, hplacement, ?_⟩
      rw [placement_vertex_decomposition, Finset.mem_union]
      exact Or.inl hboundary
    · refine ⟨placement, hplacement, ?_⟩
      rw [placement_vertex_decomposition, Finset.mem_union]
      right
      simp [hstone, hcenter]

theorem placementBoundaryVertex_has_cell {m : ℕ}
    (placement : LiteralPlacement m) {vertex : HexVertex}
    (hvertex : vertex ∈ placementBoundaryVertexFinset placement) :
    ∃ cell ∈ placement.cells, vertex ∈ cellVertexFinset cell := by
  simp only [placementBoundaryVertexFinset,
    prototypeBoundaryVertexFinset, edgeSourceFinset,
    List.mem_toFinset, List.mem_map] at hvertex
  obtain ⟨edge, hedge, hsource⟩ := hvertex
  obtain ⟨cell, hcell, hedgeCell⟩ :=
    literalPlacementBoundary_edge_has_cell placement hedge
  refine ⟨cell, hcell, ?_⟩
  simp only [cellVertexFinset, edgeSourceFinset,
    List.mem_toFinset, List.mem_map]
  exact ⟨edge, hedgeCell, hsource⟩

theorem stoneCenter_map_injective_on_tiling {m : ℕ}
    (tiling : LiteralTiling m) :
    Set.InjOn (fun placement : LiteralPlacement m =>
      upHexVertex placement.base)
      (tiling.1.filter fun placement => placement.tile = .stone) := by
  intro left hleft right hright hcenter
  have hbase : left.base = right.base :=
    upHexVertex_injective hcenter
  have hleftStone := (Finset.mem_filter.mp hleft).2
  have hrightStone := (Finset.mem_filter.mp hright).2
  apply Subtype.ext
  apply Prod.ext
  · exact hleftStone.trans hrightStone.symm
  · apply Subtype.ext
    exact hbase

theorem card_tilingStoneCenterFinset {m : ℕ}
    (tiling : LiteralTiling m) :
    (tilingStoneCenterFinset tiling).card = rightStoneCount tiling := by
  rw [tilingStoneCenterFinset, Finset.card_image_iff.mpr
    (stoneCenter_map_injective_on_tiling tiling)]
  rfl

theorem tilingBoundary_disjoint_stoneCenters {m : ℕ}
    (tiling : LiteralTiling m) :
    Disjoint (tilingBoundaryVertexFinset tiling)
      (tilingStoneCenterFinset tiling) := by
  rw [Finset.disjoint_left]
  intro vertex hboundary hcenter
  simp only [tilingBoundaryVertexFinset, Finset.mem_biUnion] at hboundary
  obtain ⟨boundaryPlacement, hboundaryPlacement,
      hboundaryVertex⟩ := hboundary
  simp only [tilingStoneCenterFinset, Finset.mem_image,
    Finset.mem_filter] at hcenter
  obtain ⟨stonePlacement, ⟨hstonePlacement, hstone⟩,
      hcenterEq⟩ := hcenter
  change stonePlacement.1.1 = .stone at hstone
  obtain ⟨cell, hcellBoundary, hcellVertex⟩ :=
    placementBoundaryVertex_has_cell boundaryPlacement hboundaryVertex
  rw [mem_cellVertexFinset_iff] at hcellVertex
  have hcellStone : cell ∈ stonePlacement.cells := by
    rcases hcellVertex with
        ⟨anchor, label, hcell, hvertex⟩ |
        ⟨anchor, label, hcell, hvertex⟩
    · have hanchor : anchor = stonePlacement.base := by
        exact upHexVertex_injective (hvertex.trans hcenterEq.symm)
      subst anchor
      rw [← hcell]
      change cellForOwnerAnchor stonePlacement.base label ∈
        placementCellList stonePlacement.1
      unfold placementCellList
      rw [hstone]
      cases label <;>
        simp [protoCells, cellForOwnerAnchor,
          translateLocalCell, c00, c10, c01,
          LiteralPlacement.base]
    · exact (upHexVertex_ne_downHexVertex stonePlacement.base anchor
        (hcenterEq.trans hvertex.symm)).elim
  let regionCell : BenzelCell (m + 5) :=
    ⟨cell, stonePlacement.2 cell hcellStone⟩
  obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
  have hboundaryEq : boundaryPlacement = covering :=
    hunique boundaryPlacement
      ⟨hboundaryPlacement, hcellBoundary⟩
  have hstoneEq : stonePlacement = covering :=
    hunique stonePlacement ⟨hstonePlacement, hcellStone⟩
  have hsame : boundaryPlacement = stonePlacement :=
    hboundaryEq.trans hstoneEq.symm
  rw [hsame] at hboundaryVertex
  apply stonePlacement_center_not_boundary stonePlacement hstone
  rw [hcenterEq]
  exact hboundaryVertex

theorem card_tilingBoundaryVertexFinset {m : ℕ}
    (tiling : LiteralTiling m) :
    (tilingBoundaryVertexFinset tiling).card +
        rightStoneCount tiling =
      Fintype.card (BenzelHexVertex m) := by
  have hdecomp := tilingCellVertexFinset_decomposition tiling
  have hfull := tilingCellVertexFinset_eq_benzel tiling
  have hcardFull := card_benzelCellVertexFinset m
  have hcardUnion := Finset.card_union_of_disjoint
    (tilingBoundary_disjoint_stoneCenters tiling)
  rw [← hdecomp, hfull, hcardFull] at hcardUnion
  rw [card_tilingStoneCenterFinset] at hcardUnion
  exact hcardUnion.symm

end BenzelProblem6Kernel
