import D4KernelOnly.GeneralCellVertexCarrier
import BenzelProblem6Kernel.TilingCellVertexUnion
import BenzelProblem6Kernel.TilingComplexVerticesGlobal
import BenzelProblem6Kernel.TilingComplexEdgeLength

/-! # Boundary vertices and symbolic length accounting -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def cmoTilingCellVertexFinset
    {s r : ℕ} (tiling : CMOLiteralTiling s r) : Finset HexVertex :=
  (offsetShadowPlacementFinset tiling).biUnion placementCellVertexFinset

noncomputable def cmoTilingBoundaryVertexFinset
    {s r : ℕ} (tiling : CMOLiteralTiling s r) : Finset HexVertex :=
  (offsetShadowPlacementFinset tiling).biUnion placementBoundaryVertexFinset

noncomputable def cmoTilingStoneCenterFinset
    {s r : ℕ} (tiling : CMOLiteralTiling s r) : Finset HexVertex :=
  ((offsetShadowPlacementFinset tiling).filter fun placement =>
    placement.tile = .stone).image fun placement => upHexVertex placement.base

theorem cmoTilingCellVertexFinset_eq_region
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    cmoTilingCellVertexFinset tiling =
      offsetCellVertexFinset (2 * s + r - 1) (3 * s + 1) := by
  ext vertex
  simp only [cmoTilingCellVertexFinset, offsetCellVertexFinset,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨placement, hplacement, hvertex⟩
    rw [placementCellVertexFinset_eq_biUnion, Finset.mem_biUnion] at hvertex
    obtain ⟨cell, hcell, hcellVertex⟩ := hvertex
    obtain ⟨source, hsource, hsourceEq⟩ :=
      (mem_offsetShadowPlacementFinset_iff tiling placement).1 hplacement
    subst placement
    rw [offsetShadowPlacement_cells] at hcell
    exact ⟨⟨cell, source.2 cell (List.mem_toFinset.mp hcell)⟩, hcellVertex⟩
  · rintro ⟨cell, hcellVertex⟩
    obtain ⟨source, hsource, hunique⟩ := tiling.2 cell
    let placement := offsetShadowPlacement source
    refine ⟨placement, ?_, ?_⟩
    · rw [mem_offsetShadowPlacementFinset_iff]
      exact ⟨source, hsource.1, rfl⟩
    · rw [placementCellVertexFinset_eq_biUnion, Finset.mem_biUnion]
      refine ⟨cell.1, ?_, hcellVertex⟩
      rw [offsetShadowPlacement_cells]
      exact List.mem_toFinset.mpr hsource.2

theorem cmoTilingCellVertex_decomposition
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    cmoTilingCellVertexFinset tiling =
      cmoTilingBoundaryVertexFinset tiling ∪
        cmoTilingStoneCenterFinset tiling := by
  ext vertex
  simp only [cmoTilingCellVertexFinset, cmoTilingBoundaryVertexFinset,
    cmoTilingStoneCenterFinset, Finset.mem_biUnion,
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

noncomputable def cmoShadowStoneCount
    {s r : ℕ} (tiling : CMOLiteralTiling s r) : ℕ :=
  ((offsetShadowPlacementFinset tiling).filter fun placement =>
    placement.tile = .stone).card

noncomputable def cmoLiteralRightStoneCount
    {s r : ℕ} (tiling : CMOLiteralTiling s r) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = .stone).card

theorem cmoShadowStoneCount_eq_literal
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    cmoShadowStoneCount tiling = cmoLiteralRightStoneCount tiling := by
  classical
  unfold cmoShadowStoneCount cmoLiteralRightStoneCount
  have heq :
      (offsetShadowPlacementFinset tiling).filter
          (fun placement => placement.tile = .stone) =
        (tiling.1.filter fun placement => placement.tile = .stone).map
          (offsetShadowPlacementEmbedding _ _) := by
    ext placement
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hplacement, hstone⟩
      obtain ⟨source, hsource, hsourceEq⟩ :=
        (mem_offsetShadowPlacementFinset_iff tiling placement).1 hplacement
      subst placement
      refine ⟨source, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hsource,
        generalToShadowTile_injective (by simpa using hstone)⟩
    · rintro ⟨source, hsource, hsourceEq⟩
      change offsetShadowPlacement source = placement at hsourceEq
      subst placement
      exact ⟨(mem_offsetShadowPlacementFinset_iff tiling _).2
          ⟨source, (Finset.mem_filter.mp hsource).1, rfl⟩,
        by
          have hsourceStone := (Finset.mem_filter.mp hsource).2
          change d4ToShadowTile source.tile = .stone
          rw [hsourceStone]
          rfl⟩
  rw [heq, Finset.card_map]

theorem cmoStoneCenter_map_injective
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    Set.InjOn (fun placement : LiteralPlacement (2 * s + r - 1) =>
      upHexVertex placement.base)
      ((offsetShadowPlacementFinset tiling).filter fun placement =>
        placement.tile = .stone) := by
  intro left hleft right hright hcenter
  have hbase : left.base = right.base := upHexVertex_injective hcenter
  have hleftStone := (Finset.mem_filter.mp hleft).2
  have hrightStone := (Finset.mem_filter.mp hright).2
  apply Subtype.ext
  apply Prod.ext
  · exact hleftStone.trans hrightStone.symm
  · apply Subtype.ext
    exact hbase

theorem card_cmoTilingStoneCenterFinset
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    (cmoTilingStoneCenterFinset tiling).card =
      cmoLiteralRightStoneCount tiling := by
  rw [cmoTilingStoneCenterFinset, Finset.card_image_iff.mpr
    (cmoStoneCenter_map_injective tiling),
    ← cmoShadowStoneCount, cmoShadowStoneCount_eq_literal]

theorem cmoBoundary_disjoint_stoneCenters
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    Disjoint (cmoTilingBoundaryVertexFinset tiling)
      (cmoTilingStoneCenterFinset tiling) := by
  rw [Finset.disjoint_left]
  intro vertex hboundary hcenter
  simp only [cmoTilingBoundaryVertexFinset, Finset.mem_biUnion] at hboundary
  obtain ⟨boundaryPlacement, hboundaryPlacement, hboundaryVertex⟩ := hboundary
  simp only [cmoTilingStoneCenterFinset, Finset.mem_image,
    Finset.mem_filter] at hcenter
  obtain ⟨stonePlacement, ⟨hstonePlacement, hstone⟩, hcenterEq⟩ := hcenter
  change stonePlacement.1.1 = .stone at hstone
  obtain ⟨cell, hcellBoundary, hcellVertex⟩ :=
    placementBoundaryVertex_has_cell boundaryPlacement hboundaryVertex
  rw [mem_cellVertexFinset_iff] at hcellVertex
  have hcellStone : cell ∈ stonePlacement.cells := by
    rcases hcellVertex with ⟨anchor, label, hcell, hvertex⟩ |
        ⟨anchor, label, hcell, hvertex⟩
    · have hanchor : anchor = stonePlacement.base :=
        upHexVertex_injective (hvertex.trans hcenterEq.symm)
      subst anchor
      rw [← hcell]
      change BenzelProblem6Kernel.cellForOwnerAnchor
        stonePlacement.base label ∈ placementCellList stonePlacement.1
      unfold placementCellList
      rw [hstone]
      cases label <;>
        simp [BenzelProblem6Kernel.protoCells,
          BenzelProblem6Kernel.cellForOwnerAnchor,
          BenzelProblem6Kernel.translateLocalCell,
          BenzelProblem6Kernel.c00, BenzelProblem6Kernel.c10,
          BenzelProblem6Kernel.c01, LiteralPlacement.base]
    · exact (upHexVertex_ne_downHexVertex stonePlacement.base anchor
        (hcenterEq.trans hvertex.symm)).elim
  have hsame : boundaryPlacement = stonePlacement :=
    cmoShadowPlacement_unique_of_cell tiling
      hboundaryPlacement hstonePlacement hcellBoundary hcellStone
  rw [hsame] at hboundaryVertex
  exact stonePlacement_center_not_boundary stonePlacement hstone
    (by rwa [hcenterEq])

theorem cmoBoundaryVertex_card_add_stones
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    (cmoTilingBoundaryVertexFinset tiling).card +
        cmoLiteralRightStoneCount tiling =
      (offsetCellVertexFinset (2 * s + r - 1) (3 * s + 1)).card := by
  have hcard := Finset.card_union_of_disjoint
    (cmoBoundary_disjoint_stoneCenters tiling)
  rw [← cmoTilingCellVertex_decomposition,
    cmoTilingCellVertexFinset_eq_region,
    card_cmoTilingStoneCenterFinset] at hcard
  exact hcard.symm

theorem cmoShadowPlacementFinset_card
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    (offsetShadowPlacementFinset tiling).card = tiling.1.card := by
  rw [offsetShadowPlacementFinset, Finset.card_map]

theorem listStoneCount_cmoShadow
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    listStoneCount (offsetShadowPlacementFinset tiling).toList =
      cmoLiteralRightStoneCount tiling := by
  have hfilter := length_filter_toList_bool
    (offsetShadowPlacementFinset tiling)
      (fun placement => placement.tile = .stone)
  rw [← cmoShadowStoneCount_eq_literal tiling]
  simpa [listStoneCount, cmoShadowStoneCount] using hfilter

theorem reverseCMOPlacementBoundary_length_identity
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    (reverseLiteralPlacementBoundaryList
        (offsetShadowPlacementFinset tiling).toList).length +
      2 * cmoLiteralRightStoneCount tiling =
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
  have hpartition' : cmoLiteralRightStoneCount tiling +
      listBoneCount (offsetShadowPlacementFinset tiling).toList =
        (offsetShadowPlacementFinset tiling).toList.length := by
    rw [← listStoneCount_cmoShadow tiling]
    exact hpartition
  rw [reverseLiteralPlacementBoundaryList_length, listStoneCount_cmoShadow]
  rw [← Finset.length_toList]
  change 12 * cmoLiteralRightStoneCount tiling +
      14 * listBoneCount placements +
      2 * cmoLiteralRightStoneCount tiling = 14 * placements.length
  change cmoLiteralRightStoneCount tiling + listBoneCount placements =
    placements.length at hpartition'
  omega

end FiniteDefects
