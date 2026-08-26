import D4KernelOnly.D4VertexAnchorCount
import BenzelProblem6Kernel.TilingCellVertexUnion
import BenzelProblem6Kernel.TilingComplexVerticesGlobal
import BenzelProblem6Kernel.TilingComplexEdgeLength

/-! # Boundary vertices and exact length accounting for d=4 tilings -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def d4TilingCellVertexFinset {m : ℕ}
    (tiling : D4LiteralTiling m) : Finset HexVertex :=
  (d4ShadowPlacementFinset tiling).biUnion placementCellVertexFinset

noncomputable def d4TilingBoundaryVertexFinset {m : ℕ}
    (tiling : D4LiteralTiling m) : Finset HexVertex :=
  (d4ShadowPlacementFinset tiling).biUnion placementBoundaryVertexFinset

noncomputable def d4TilingStoneCenterFinset {m : ℕ}
    (tiling : D4LiteralTiling m) : Finset HexVertex :=
  ((d4ShadowPlacementFinset tiling).filter fun placement =>
    placement.tile = .stone).image fun placement =>
      upHexVertex placement.base

theorem d4TilingCellVertexFinset_eq_region {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4TilingCellVertexFinset tiling = d4CellVertexFinset m := by
  ext vertex
  simp only [d4TilingCellVertexFinset, d4CellVertexFinset,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨placement, hplacement, hvertex⟩
    rw [placementCellVertexFinset_eq_biUnion,
      Finset.mem_biUnion] at hvertex
    obtain ⟨cell, hcell, hcellVertex⟩ := hvertex
    obtain ⟨source, hsource, hsourceEq⟩ :=
      (mem_d4ShadowPlacementFinset_iff tiling placement).1 hplacement
    subst placement
    rw [d4ShadowPlacement_cells] at hcell
    exact ⟨⟨cell, source.2 cell (List.mem_toFinset.mp hcell)⟩, hcellVertex⟩
  · rintro ⟨cell, hcellVertex⟩
    obtain ⟨source, hsource, hunique⟩ := tiling.2 cell
    let placement := d4ShadowPlacement source
    refine ⟨placement, ?_, ?_⟩
    · rw [mem_d4ShadowPlacementFinset_iff]
      exact ⟨source, hsource.1, rfl⟩
    · rw [placementCellVertexFinset_eq_biUnion,
        Finset.mem_biUnion]
      refine ⟨cell.1, ?_, hcellVertex⟩
      rw [d4ShadowPlacement_cells]
      exact List.mem_toFinset.mpr hsource.2

theorem d4TilingCellVertex_decomposition {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4TilingCellVertexFinset tiling =
      d4TilingBoundaryVertexFinset tiling ∪
        d4TilingStoneCenterFinset tiling := by
  ext vertex
  simp only [d4TilingCellVertexFinset, d4TilingBoundaryVertexFinset,
    d4TilingStoneCenterFinset, Finset.mem_biUnion,
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

noncomputable def d4ShadowStoneCount {m : ℕ}
    (tiling : D4LiteralTiling m) : ℕ :=
  ((d4ShadowPlacementFinset tiling).filter fun placement =>
    placement.tile = .stone).card

theorem d4ShadowStoneCount_eq_kernel {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4ShadowStoneCount tiling = d4KernelRightStoneCount tiling := by
  classical
  unfold d4ShadowStoneCount d4KernelRightStoneCount
  have heq :
      (d4ShadowPlacementFinset tiling).filter
          (fun placement => placement.tile = .stone) =
        (tiling.1.filter fun placement => placement.tile = .stone).map
          (d4ShadowPlacementEmbedding m) := by
    ext placement
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hplacement, hstone⟩
      obtain ⟨source, hsource, hsourceEq⟩ :=
        (mem_d4ShadowPlacementFinset_iff tiling placement).1 hplacement
      subst placement
      refine ⟨source, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hsource,
        d4ToShadowTile_injective (by simpa using hstone)⟩
    · rintro ⟨source, hsource, hsourceEq⟩
      change d4ShadowPlacement source = placement at hsourceEq
      subst placement
      exact ⟨(mem_d4ShadowPlacementFinset_iff tiling _).2
          ⟨source, (Finset.mem_filter.mp hsource).1, rfl⟩,
        by
          have hsourceStone := (Finset.mem_filter.mp hsource).2
          change d4ToShadowTile source.tile = .stone
          rw [hsourceStone]
          rfl⟩
  rw [heq, Finset.card_map]

theorem d4StoneCenter_map_injective {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Set.InjOn (fun placement : LiteralPlacement m =>
      upHexVertex placement.base)
      ((d4ShadowPlacementFinset tiling).filter fun placement =>
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

theorem card_d4TilingStoneCenterFinset {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TilingStoneCenterFinset tiling).card =
      d4KernelRightStoneCount tiling := by
  rw [d4TilingStoneCenterFinset, Finset.card_image_iff.mpr
    (d4StoneCenter_map_injective tiling),
    ← d4ShadowStoneCount, d4ShadowStoneCount_eq_kernel]

theorem d4Boundary_disjoint_stoneCenters {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Disjoint (d4TilingBoundaryVertexFinset tiling)
      (d4TilingStoneCenterFinset tiling) := by
  rw [Finset.disjoint_left]
  intro vertex hboundary hcenter
  simp only [d4TilingBoundaryVertexFinset, Finset.mem_biUnion] at hboundary
  obtain ⟨boundaryPlacement, hboundaryPlacement,
    hboundaryVertex⟩ := hboundary
  simp only [d4TilingStoneCenterFinset, Finset.mem_image,
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
    · have hanchor : anchor = stonePlacement.base :=
        upHexVertex_injective (hvertex.trans hcenterEq.symm)
      subst anchor
      rw [← hcell]
      change BenzelProblem6Kernel.cellForOwnerAnchor
        stonePlacement.base label ∈
        placementCellList stonePlacement.1
      unfold placementCellList
      rw [hstone]
      cases label <;>
        simp [BenzelProblem6Kernel.protoCells,
          BenzelProblem6Kernel.cellForOwnerAnchor,
          BenzelProblem6Kernel.translateLocalCell,
          BenzelProblem6Kernel.c00, BenzelProblem6Kernel.c10,
          BenzelProblem6Kernel.c01,
          LiteralPlacement.base]
    · exact (upHexVertex_ne_downHexVertex stonePlacement.base anchor
        (hcenterEq.trans hvertex.symm)).elim
  have hsame : boundaryPlacement = stonePlacement :=
    d4ShadowPlacement_unique_of_cell tiling
      hboundaryPlacement hstonePlacement hcellBoundary hcellStone
  rw [hsame] at hboundaryVertex
  exact stonePlacement_center_not_boundary stonePlacement hstone
    (by rwa [hcenterEq])

theorem d4BoundaryVertex_card_add_stones {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TilingBoundaryVertexFinset tiling).card +
        d4KernelRightStoneCount tiling =
      (d4CellVertexFinset m).card := by
  have hcard := Finset.card_union_of_disjoint
    (d4Boundary_disjoint_stoneCenters tiling)
  rw [← d4TilingCellVertex_decomposition,
    d4TilingCellVertexFinset_eq_region,
    card_d4TilingStoneCenterFinset] at hcard
  exact hcard.symm

theorem d4ShadowPlacementFinset_card {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ShadowPlacementFinset tiling).card = tiling.1.card := by
  rw [d4ShadowPlacementFinset, Finset.card_map]

theorem listStoneCount_d4Shadow {m : ℕ}
    (tiling : D4LiteralTiling m) :
    listStoneCount (d4ShadowPlacementFinset tiling).toList =
      d4KernelRightStoneCount tiling := by
  have hfilter := length_filter_toList_bool
    (d4ShadowPlacementFinset tiling)
      (fun placement => placement.tile = .stone)
  rw [← d4ShadowStoneCount_eq_kernel tiling]
  simpa [listStoneCount, d4ShadowStoneCount] using hfilter

theorem reverseD4PlacementBoundary_length_identity {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (reverseLiteralPlacementBoundaryList
        (d4ShadowPlacementFinset tiling).toList).length +
      2 * d4KernelRightStoneCount tiling =
        14 * (d4ShadowPlacementFinset tiling).card := by
  let placements := (d4ShadowPlacementFinset tiling).toList
  have hpartition : listStoneCount placements + listBoneCount placements =
      placements.length := by
    induction placements with
    | nil => rfl
    | cons placement rest ih =>
        cases htile : placement.tile
        all_goals simp [listStoneCount, listBoneCount, htile] at ih ⊢
        all_goals omega
  have hpartition' : d4KernelRightStoneCount tiling +
      listBoneCount (d4ShadowPlacementFinset tiling).toList =
        (d4ShadowPlacementFinset tiling).toList.length := by
    rw [← listStoneCount_d4Shadow tiling]
    exact hpartition
  rw [reverseLiteralPlacementBoundaryList_length,
    listStoneCount_d4Shadow]
  rw [← Finset.length_toList]
  change 12 * d4KernelRightStoneCount tiling +
      14 * listBoneCount placements +
      2 * d4KernelRightStoneCount tiling = 14 * placements.length
  change d4KernelRightStoneCount tiling + listBoneCount placements =
    placements.length at hpartition'
  omega

theorem d4TilePerimeterVertex_identity {m : ℕ}
    (tiling : D4LiteralTiling m) :
    12 * (d4ShadowPlacementFinset tiling).card +
        (12 * m + 24) + 2 =
      2 * (d4CellVertexFinset m).card := by
  rw [d4ShadowPlacementFinset_card, d4_literal_tiling_card,
    twice_card_d4CellVertexFinset]
  have hchoose := Nat.choose_succ_right_eq (m + 4) 1
  norm_num at hchoose
  have hge : 2 ≤ (m + 4).choose 2 := by nlinarith
  have hsub : (m + 4).choose 2 - 2 + 2 =
      (m + 4).choose 2 := Nat.sub_add_cancel hge
  nlinarith

end FiniteDefects
