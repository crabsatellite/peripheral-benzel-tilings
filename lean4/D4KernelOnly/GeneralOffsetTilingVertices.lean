import D4KernelOnly.GeneralClassZeroTilingComplex
import BenzelProblem6Kernel.TilingComplexVerticesGlobal
import BenzelProblem6Kernel.TilingComplexEdgeLength

/-! # Boundary vertices and symbolic length accounting for any offset tiling -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def offsetTilingCellVertexFinset
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) : Finset HexVertex :=
  (offsetShadowPlacementFinset tiling).biUnion placementCellVertexFinset

noncomputable def offsetTilingBoundaryVertexFinset
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) : Finset HexVertex :=
  (offsetShadowPlacementFinset tiling).biUnion placementBoundaryVertexFinset

noncomputable def offsetTilingStoneCenterFinset
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) : Finset HexVertex :=
  ((offsetShadowPlacementFinset tiling).filter fun placement =>
    placement.tile = .stone).image fun placement => upHexVertex placement.base

def offsetLiteralStoneCount
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = .stone).card

theorem offsetTilingCellVertexFinset_eq_region
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    offsetTilingCellVertexFinset tiling = offsetCellVertexFinset t d := by
  ext vertex
  simp only [offsetTilingCellVertexFinset, offsetCellVertexFinset,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨placement, hplacement, hvertex⟩
    rw [placementCellVertexFinset_eq_biUnion, Finset.mem_biUnion] at hvertex
    obtain ⟨cell, hcell, hcellVertex⟩ := hvertex
    obtain ⟨source, hsource, rfl⟩ :=
      (mem_offsetShadowPlacementFinset_iff tiling placement).1 hplacement
    rw [offsetShadowPlacement_cells] at hcell
    exact ⟨⟨cell, source.2 cell (List.mem_toFinset.mp hcell)⟩, hcellVertex⟩
  · rintro ⟨cell, hcellVertex⟩
    obtain ⟨source, hsource, hunique⟩ := tiling.2 cell
    refine ⟨offsetShadowPlacement source, ?_, ?_⟩
    · rw [mem_offsetShadowPlacementFinset_iff]
      exact ⟨source, hsource.1, rfl⟩
    · rw [placementCellVertexFinset_eq_biUnion, Finset.mem_biUnion,
        offsetShadowPlacement_cells]
      exact ⟨cell.1, List.mem_toFinset.mpr hsource.2, hcellVertex⟩

theorem offsetTilingCellVertex_decomposition
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    offsetTilingCellVertexFinset tiling =
      offsetTilingBoundaryVertexFinset tiling ∪ offsetTilingStoneCenterFinset tiling := by
  ext vertex
  simp only [offsetTilingCellVertexFinset, offsetTilingBoundaryVertexFinset,
    offsetTilingStoneCenterFinset, Finset.mem_biUnion,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨placement, hplacement, hvertex⟩
    rw [placement_vertex_decomposition, Finset.mem_union] at hvertex
    rcases hvertex with hb | hc
    · exact Or.inl ⟨placement, hplacement, hb⟩
    · by_cases hs : placement.tile = .stone
      · simp [hs] at hc
        exact Or.inr ⟨placement, ⟨hplacement, hs⟩, hc.symm⟩
      · simp [hs] at hc
  · rintro (⟨placement, hp, hb⟩ | ⟨placement, ⟨hp, hs⟩, hc⟩)
    · refine ⟨placement, hp, ?_⟩
      rw [placement_vertex_decomposition, Finset.mem_union]
      exact Or.inl hb
    · refine ⟨placement, hp, ?_⟩
      rw [placement_vertex_decomposition, Finset.mem_union]
      right
      simp [hs, hc]

theorem offsetShadowStoneCount_eq_literal
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    ((offsetShadowPlacementFinset tiling).filter fun placement =>
        placement.tile = .stone).card = offsetLiteralStoneCount tiling := by
  classical
  have heq :
      (offsetShadowPlacementFinset tiling).filter
          (fun placement => placement.tile = .stone) =
        (tiling.1.filter fun placement => placement.tile = .stone).map
          (offsetShadowPlacementEmbedding _ _) := by
    ext placement
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hp, hs⟩
      obtain ⟨source, hsource, rfl⟩ :=
        (mem_offsetShadowPlacementFinset_iff tiling placement).1 hp
      refine ⟨source, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hsource,
        generalToShadowTile_injective (by simpa using hs)⟩
    · rintro ⟨source, hsource, hEq⟩
      change offsetShadowPlacement source = placement at hEq
      subst placement
      exact ⟨(mem_offsetShadowPlacementFinset_iff tiling _).2
          ⟨source, (Finset.mem_filter.mp hsource).1, rfl⟩,
        by
          have hs := (Finset.mem_filter.mp hsource).2
          change d4ToShadowTile source.tile = .stone
          rw [hs]
          rfl⟩
  rw [heq, Finset.card_map]
  rfl

theorem offsetStoneCenter_map_injective
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    Set.InjOn (fun placement : LiteralPlacement t => upHexVertex placement.base)
      ((offsetShadowPlacementFinset tiling).filter fun placement =>
        placement.tile = .stone) := by
  intro left hleft right hright hcenter
  have hbase : left.base = right.base := upHexVertex_injective hcenter
  have hl := (Finset.mem_filter.mp hleft).2
  have hr := (Finset.mem_filter.mp hright).2
  apply Subtype.ext
  apply Prod.ext
  · exact hl.trans hr.symm
  · apply Subtype.ext
    exact hbase

theorem card_offsetTilingStoneCenterFinset
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    (offsetTilingStoneCenterFinset tiling).card = offsetLiteralStoneCount tiling := by
  rw [offsetTilingStoneCenterFinset, Finset.card_image_iff.mpr
    (offsetStoneCenter_map_injective tiling), ← offsetShadowStoneCount_eq_literal]

theorem offsetBoundary_disjoint_stoneCenters
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    Disjoint (offsetTilingBoundaryVertexFinset tiling)
      (offsetTilingStoneCenterFinset tiling) := by
  rw [Finset.disjoint_left]
  intro vertex hb hc
  simp only [offsetTilingBoundaryVertexFinset, Finset.mem_biUnion] at hb
  obtain ⟨boundaryPlacement, hbp, hbvertex⟩ := hb
  simp only [offsetTilingStoneCenterFinset, Finset.mem_image,
    Finset.mem_filter] at hc
  obtain ⟨stonePlacement, ⟨hsp, hstone⟩, hcenter⟩ := hc
  change stonePlacement.1.1 = .stone at hstone
  obtain ⟨cell, hcellBoundary, hcellVertex⟩ :=
    placementBoundaryVertex_has_cell boundaryPlacement hbvertex
  rw [mem_cellVertexFinset_iff] at hcellVertex
  have hcellStone : cell ∈ stonePlacement.cells := by
    rcases hcellVertex with ⟨anchor, label, hcell, hvertex⟩ |
        ⟨anchor, label, hcell, hvertex⟩
    · have hanchor : anchor = stonePlacement.base :=
        upHexVertex_injective (hvertex.trans hcenter.symm)
      subst anchor
      rw [← hcell]
      change BenzelProblem6Kernel.cellForOwnerAnchor stonePlacement.base label ∈
        placementCellList stonePlacement.1
      unfold placementCellList
      rw [hstone]
      cases label <;> simp [BenzelProblem6Kernel.protoCells,
        BenzelProblem6Kernel.cellForOwnerAnchor,
        BenzelProblem6Kernel.translateLocalCell,
        BenzelProblem6Kernel.c00, BenzelProblem6Kernel.c10,
        BenzelProblem6Kernel.c01, LiteralPlacement.base]
    · exact (upHexVertex_ne_downHexVertex stonePlacement.base anchor
        (hcenter.trans hvertex.symm)).elim
  have hsame : boundaryPlacement = stonePlacement :=
    offsetShadowPlacement_unique_of_cell tiling hbp hsp hcellBoundary hcellStone
  rw [hsame] at hbvertex
  exact stonePlacement_center_not_boundary stonePlacement hstone (by rwa [hcenter])

theorem offsetBoundaryVertex_card_add_stones
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    (offsetTilingBoundaryVertexFinset tiling).card + offsetLiteralStoneCount tiling =
      (offsetCellVertexFinset t d).card := by
  have hcard := Finset.card_union_of_disjoint
    (offsetBoundary_disjoint_stoneCenters tiling)
  rw [← offsetTilingCellVertex_decomposition,
    offsetTilingCellVertexFinset_eq_region,
    card_offsetTilingStoneCenterFinset] at hcard
  exact hcard.symm

theorem offsetShadowPlacementFinset_card
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    (offsetShadowPlacementFinset tiling).card = tiling.1.card := by
  rw [offsetShadowPlacementFinset, Finset.card_map]

theorem reverseOffsetPlacementBoundary_length_identity
    {t d : ℕ} (tiling : OffsetLiteralTiling t d) :
    (reverseLiteralPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList).length +
      2 * offsetLiteralStoneCount tiling =
        14 * (offsetShadowPlacementFinset tiling).card := by
  let placements := (offsetShadowPlacementFinset tiling).toList
  have hpartition : listStoneCount placements + listBoneCount placements =
      placements.length := by
    induction placements with
    | nil => rfl
    | cons placement rest ih =>
      cases htile : placement.tile
      all_goals simp [listStoneCount, listBoneCount, htile] at ih ⊢
      all_goals omega
  have hstone : listStoneCount placements = offsetLiteralStoneCount tiling := by
    have hfilter := length_filter_toList_bool
      (offsetShadowPlacementFinset tiling) (fun p => p.tile = .stone)
    rw [← offsetShadowStoneCount_eq_literal tiling]
    simpa [placements, listStoneCount] using hfilter
  rw [reverseLiteralPlacementBoundaryList_length, hstone,
    ← Finset.length_toList]
  rw [hstone] at hpartition
  change offsetLiteralStoneCount tiling + listBoneCount placements =
    placements.length at hpartition
  change 12 * offsetLiteralStoneCount tiling + 14 * listBoneCount placements +
      2 * offsetLiteralStoneCount tiling = 14 * placements.length
  omega

end FiniteDefects
