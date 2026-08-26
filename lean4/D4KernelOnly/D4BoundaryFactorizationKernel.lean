import D4KernelOnly.D4TreeContourWord
import FiniteDefects.D4ConwayLagariasInterface

/-! # Premise-free literal d=4 boundary factorization -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 800000

noncomputable def d4ReducedGeometricPeeling {m : ℕ}
    (tiling : D4LiteralTiling m) :
    GeometricBoundaryPeeling m (d4ReducedBoundaryWalk m) :=
  (d4ReducedRightmostSkeleton tiling).toGeometricPeeling
    (d4ReducedRightmostTerminal_word_empty tiling)

theorem d4ReducedGeometricPeeling_placements {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ReducedGeometricPeeling tiling).placements =
      (d4ReducedRightmostSkeleton tiling).removedPlacements := by
  exact (d4ReducedRightmostSkeleton tiling).toGeometricPeeling_placements
    (d4ReducedRightmostTerminal_word_empty tiling)

theorem d4ReducedGeometricPeeling_placements_perm {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List.Perm (d4ReducedGeometricPeeling tiling).placements
      (d4ShadowPlacementFinset tiling).toList := by
  rw [d4ReducedGeometricPeeling_placements]
  exact (d4ReducedRightmostSkeleton tiling).removedPlacements_perm

theorem shadowFactorTileCount_eq_factorProtoTileCount
    (factors : List ConwayLagariasWordFactor)
    (tile : BenzelProblem6Kernel.ProtoTile) :
    shadowFactorTileCount factors tile = factorProtoTileCount factors tile := by
  induction factors with
  | nil => rfl
  | cons factor rest ih =>
      simp [shadowFactorTileCount, factorProtoTileCount, ih]

theorem d4LiteralProtoTileCount_eq_toList_map_count {m : ℕ}
    (tiling : D4LiteralTiling m) (tile : FiniteDefects.ProtoTile) :
    d4LiteralProtoTileCount tiling tile =
      (tiling.1.toList.map D4LiteralPlacement.tile).count tile := by
  rw [List.count_eq_countP, List.countP_eq_length_filter,
    List.filter_map, List.length_map]
  let filtered := tiling.1.toList.filter
    (fun placement => placement.tile == tile)
  have hnodup : filtered.Nodup := (Finset.nodup_toList tiling.1).filter _
  change d4LiteralProtoTileCount tiling tile = filtered.length
  rw [← List.toFinset_card_of_nodup hnodup]
  unfold d4LiteralProtoTileCount
  apply congrArg Finset.card
  dsimp [filtered]
  rw [List.toFinset_filter, Finset.toList_toFinset]
  ext placement
  simp only [Finset.mem_filter, beq_iff_eq]

theorem d4ShadowPlacement_tile_list {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ShadowPlacementList tiling).map LiteralPlacement.tile =
      (tiling.1.toList.map D4LiteralPlacement.tile).map d4ToShadowTile := by
  unfold d4ShadowPlacementList
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro placement hplacement
  exact d4ShadowPlacement_tile placement

theorem d4ShadowPlacementFinset_tile_count {m : ℕ}
    (tiling : D4LiteralTiling m) (tile : FiniteDefects.ProtoTile) :
    ((d4ShadowPlacementFinset tiling).toList.map
      LiteralPlacement.tile).count (d4ToShadowTile tile) =
      d4LiteralProtoTileCount tiling tile := by
  have hperm := (d4ShadowPlacementFinset_toList_perm tiling).map
    LiteralPlacement.tile
  rw [hperm.count_eq, d4ShadowPlacement_tile_list]
  rw [List.count_map_of_injective _ _ d4ToShadowTile_injective]
  exact (d4LiteralProtoTileCount_eq_toList_map_count tiling tile).symm

theorem d4ReducedBoundary_has_factorization {m : ℕ}
    (tiling : D4LiteralTiling m) :
    HasConwayLagariasWordFactorization
      (labeledEdgeWord (d4ReducedBoundaryWalk m))
      (d4ReducedGeometricPeeling tiling).factors :=
  (d4ReducedGeometricPeeling tiling).hasFactorization

theorem d4LiteralBoundary_has_factorization {m : ℕ}
    (tiling : D4LiteralTiling m) :
    HasConwayLagariasWordFactorization
      (d4LiteralBoundaryLabels m)
      (d4ReducedGeometricPeeling tiling).factors := by
  have hreduce := reduceGeometricBacktracks_word_equivalent
    (d4LiteralBoundaryWalk m)
  have hfactor := d4ReducedBoundary_has_factorization tiling
  have htrans := Relation.EqvGen.trans _ _ _ hreduce hfactor
  simpa [d4ReducedBoundaryWalk, d4LiteralBoundaryWalk_labels] using htrans

noncomputable def d4LiteralBoundaryFactorizationKernel {m : ℕ}
    (tiling : D4LiteralTiling m) :
    D4LiteralBoundaryFactorization tiling where
  factors := (d4ReducedGeometricPeeling tiling).factors
  boundary_equivalent := d4LiteralBoundary_has_factorization tiling
  tile_count_exact := by
    intro tile
    rw [shadowFactorTileCount_eq_factorProtoTileCount,
      (d4ReducedGeometricPeeling tiling).factorProtoTileCount_eq_placementCount,
      (d4ReducedGeometricPeeling_placements_perm tiling).map
        LiteralPlacement.tile |>.count_eq,
      d4ShadowPlacementFinset_tile_count]

theorem d4LiteralBoundaryFactorizationStatement_proved :
    D4LiteralBoundaryFactorizationStatement := by
  intro m tiling
  exact ⟨d4LiteralBoundaryFactorizationKernel tiling⟩

theorem d4KernelStoneStatement_proved : D4KernelStoneStatement :=
  d4KernelStoneStatement_of_boundaryFactorization
    d4LiteralBoundaryFactorizationStatement_proved

theorem d4ConwayLagariasStatement_proved : D4ConwayLagariasStatement := by
  intro m tiling
  exact d4KernelStoneStatement_proved m tiling

end FiniteDefects
