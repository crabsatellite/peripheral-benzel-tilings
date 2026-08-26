import D4KernelOnly.GeneralClassMinusOneTreeContourWord
import D4KernelOnly.D4BoundaryFactorizationKernel

/-! # Premise-free class-minus-one boundary factorization and bone count -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def cmoReducedGeometricPeeling
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    GeometricBoundaryPeeling (2 * s + r - 1) (cmoReducedBoundaryWalk s r) :=
  (cmoReducedRightmostSkeleton hs tiling).toGeometricPeeling
    (cmoReducedRightmostTerminal_word_empty hs tiling)

theorem cmoReducedGeometricPeeling_placements
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoReducedGeometricPeeling hs tiling).placements =
      (cmoReducedRightmostSkeleton hs tiling).removedPlacements :=
  (cmoReducedRightmostSkeleton hs tiling).toGeometricPeeling_placements
    (cmoReducedRightmostTerminal_word_empty hs tiling)

theorem cmoReducedGeometricPeeling_placements_perm
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    List.Perm (cmoReducedGeometricPeeling hs tiling).placements
      (offsetShadowPlacementFinset tiling).toList := by
  rw [cmoReducedGeometricPeeling_placements]
  exact (cmoReducedRightmostSkeleton hs tiling).removedPlacements_perm

def cmoLiteralProtoTileCount
    {s r : ℕ} (tiling : CMOLiteralTiling s r) (tile : ProtoTile) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = tile).card

theorem cmoLiteralProtoTileCount_eq_toList_map_count
    {s r : ℕ} (tiling : CMOLiteralTiling s r) (tile : ProtoTile) :
    cmoLiteralProtoTileCount tiling tile =
      (tiling.1.toList.map OffsetLiteralPlacement.tile).count tile := by
  rw [List.count_eq_countP, List.countP_eq_length_filter,
    List.filter_map, List.length_map]
  let filtered := tiling.1.toList.filter
    (fun placement => placement.tile == tile)
  have hnodup : filtered.Nodup := (Finset.nodup_toList tiling.1).filter _
  change cmoLiteralProtoTileCount tiling tile = filtered.length
  rw [← List.toFinset_card_of_nodup hnodup]
  unfold cmoLiteralProtoTileCount
  apply congrArg Finset.card
  dsimp [filtered]
  rw [List.toFinset_filter, Finset.toList_toFinset]
  ext placement
  simp only [Finset.mem_filter, beq_iff_eq]

theorem cmoShadowPlacement_tile_list
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    (offsetShadowPlacementList tiling).map LiteralPlacement.tile =
      (tiling.1.toList.map OffsetLiteralPlacement.tile).map d4ToShadowTile := by
  unfold offsetShadowPlacementList
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro placement hplacement
  exact offsetShadowPlacement_tile placement

theorem cmoShadowPlacementFinset_tile_count
    {s r : ℕ} (tiling : CMOLiteralTiling s r) (tile : ProtoTile) :
    ((offsetShadowPlacementFinset tiling).toList.map
      LiteralPlacement.tile).count (d4ToShadowTile tile) =
      cmoLiteralProtoTileCount tiling tile := by
  have hperm := (cmoShadowPlacementFinset_toList_perm tiling).map
    LiteralPlacement.tile
  rw [hperm.count_eq, cmoShadowPlacement_tile_list]
  rw [List.count_map_of_injective _ _ generalToShadowTile_injective]
  exact (cmoLiteralProtoTileCount_eq_toList_map_count tiling tile).symm

theorem cmoReducedBoundary_has_factorization
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    HasConwayLagariasWordFactorization
      (labeledEdgeWord (cmoReducedBoundaryWalk s r))
      (cmoReducedGeometricPeeling hs tiling).factors :=
  (cmoReducedGeometricPeeling hs tiling).hasFactorization

theorem cmoLiteralBoundary_has_factorization
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    HasConwayLagariasWordFactorization
      (classMinusOneLiteralBoundaryLabels s r)
      (cmoReducedGeometricPeeling hs tiling).factors := by
  have hreduce := reduceGeometricBacktracks_word_equivalent
    (classMinusOneLiteralBoundaryWalk s r)
  have hfactor := cmoReducedBoundary_has_factorization hs tiling
  have htrans := Relation.EqvGen.trans _ _ _ hreduce hfactor
  simpa [cmoReducedBoundaryWalk,
    classMinusOneLiteralBoundaryWalk_labels] using htrans

theorem twice_cmoLiteralRightStoneCount
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    2 * cmoLiteralRightStoneCount tiling =
      s * s + r * r + s + r - 2 * s * r := by
  let factors := (cmoReducedGeometricPeeling hs tiling).factors
  have hfactorization := cmoLiteralBoundary_has_factorization hs tiling
  have hfactorIdentity :=
    boundary_identity_of_conwayLagarias_factorization hfactorization
  have houter := classMinusOneLiteralBoundary_identityWord s r
  have hsummary := hfactorIdentity.2.symm.trans houter.2
  have harea := congrArg ShadowSummary.areaNumerator hsummary
  have hfactor := shadowFactorArea_eq_stones factors
  have hcount : shadowFactorTileCount factors .stone =
      cmoLiteralRightStoneCount tiling := by
    change shadowFactorTileCount factors (d4ToShadowTile .stone) = _
    rw [shadowFactorTileCount_eq_factorProtoTileCount,
      (cmoReducedGeometricPeeling hs tiling).factorProtoTileCount_eq_placementCount,
      (cmoReducedGeometricPeeling_placements_perm hs tiling).map
        LiteralPlacement.tile |>.count_eq,
      cmoShadowPlacementFinset_tile_count]
    rfl
  rw [hcount] at hfactor
  rw [hfactor] at harea
  change 18 * (cmoLiteralRightStoneCount tiling : ℤ) =
    9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
      (r : ℤ) ^ 2 + (s : ℤ) + (r : ℤ)) at harea
  have hnonneg : 2 * s * r ≤ s * s + r * r + s + r := by
    have hsq := two_mul_le_add_sq s r
    simpa [pow_two, Nat.add_assoc] using
      le_trans hsq (Nat.le_add_right _ (s + r))
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hnonneg]
  push_cast
  nlinarith

theorem cmo_stone_add_bone_eq_tiles
    {s r : ℕ} (tiling : CMOLiteralTiling s r) :
    cmoLiteralRightStoneCount tiling + offsetBoneCount tiling = tiling.1.card := by
  classical
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := tiling.1) (fun placement => placement.tile = .stone)
  exact hpartition

theorem cmo_bone_count_kernelOnly
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    offsetBoneCount tiling = 3 * s * r := by
  have htiles := twice_cmo_tiling_card hs tiling
  have hstones := twice_cmoLiteralRightStoneCount hs tiling
  have hpartition := cmo_stone_add_bone_eq_tiles tiling
  have hnonneg : 2 * s * r ≤ s * s + r * r + s + r := by
    have hsq := two_mul_le_add_sq s r
    simpa [pow_two, Nat.add_assoc] using
      le_trans hsq (Nat.le_add_right _ (s + r))
  have htilesZ := congrArg (fun n : ℕ => (n : ℤ)) htiles
  have hstonesZ := congrArg (fun n : ℕ => (n : ℤ)) hstones
  have hpartitionZ := congrArg (fun n : ℕ => (n : ℤ)) hpartition
  push_cast at htilesZ hstonesZ hpartitionZ
  rw [Nat.cast_sub hnonneg] at hstonesZ
  push_cast at hstonesZ
  apply Nat.cast_injective (R := ℤ)
  push_cast
  nlinarith [htilesZ, hstonesZ, hpartitionZ]

end FiniteDefects
