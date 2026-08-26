import D4KernelOnly.GeneralClassZeroTreeContourWord
import D4KernelOnly.GeneralClassMinusOneBoneCount

/-! # Premise-free class-zero boundary factorization and bone count -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def czReducedGeometricPeeling
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    GeometricBoundaryPeeling (2 * s + r - 2) (czReducedBoundaryWalk s r) :=
  (czReducedRightmostSkeleton hs hr tiling).toGeometricPeeling
    (czReducedRightmostTerminal_word_empty hs hr tiling)

theorem czReducedGeometricPeeling_placements
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czReducedGeometricPeeling hs hr tiling).placements =
      (czReducedRightmostSkeleton hs hr tiling).removedPlacements :=
  (czReducedRightmostSkeleton hs hr tiling).toGeometricPeeling_placements
    (czReducedRightmostTerminal_word_empty hs hr tiling)

theorem czReducedGeometricPeeling_placements_perm
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    List.Perm (czReducedGeometricPeeling hs hr tiling).placements
      (offsetShadowPlacementFinset tiling).toList := by
  rw [czReducedGeometricPeeling_placements]
  exact (czReducedRightmostSkeleton hs hr tiling).removedPlacements_perm

def czLiteralProtoTileCount
    {s r : ℕ} (tiling : CZLiteralTiling s r) (tile : ProtoTile) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = tile).card

theorem czLiteralProtoTileCount_eq_toList_map_count
    {s r : ℕ} (tiling : CZLiteralTiling s r) (tile : ProtoTile) :
    czLiteralProtoTileCount tiling tile =
      (tiling.1.toList.map OffsetLiteralPlacement.tile).count tile := by
  rw [List.count_eq_countP, List.countP_eq_length_filter,
    List.filter_map, List.length_map]
  let filtered := tiling.1.toList.filter (fun placement => placement.tile == tile)
  have hnodup : filtered.Nodup := (Finset.nodup_toList tiling.1).filter _
  change czLiteralProtoTileCount tiling tile = filtered.length
  rw [← List.toFinset_card_of_nodup hnodup]
  unfold czLiteralProtoTileCount
  apply congrArg Finset.card
  dsimp [filtered]
  rw [List.toFinset_filter, Finset.toList_toFinset]
  ext placement
  simp only [Finset.mem_filter, beq_iff_eq]

theorem czShadowPlacement_tile_list
    {s r : ℕ} (tiling : CZLiteralTiling s r) :
    (offsetShadowPlacementList tiling).map LiteralPlacement.tile =
      (tiling.1.toList.map OffsetLiteralPlacement.tile).map d4ToShadowTile := by
  unfold offsetShadowPlacementList
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro placement hp
  exact offsetShadowPlacement_tile placement

theorem czShadowPlacementFinset_tile_count
    {s r : ℕ} (tiling : CZLiteralTiling s r) (tile : ProtoTile) :
    ((offsetShadowPlacementFinset tiling).toList.map LiteralPlacement.tile).count
        (d4ToShadowTile tile) = czLiteralProtoTileCount tiling tile := by
  have hperm := (offsetShadowPlacementFinset_toList_perm tiling).map
    LiteralPlacement.tile
  rw [hperm.count_eq, czShadowPlacement_tile_list]
  rw [List.count_map_of_injective _ _ generalToShadowTile_injective]
  exact (czLiteralProtoTileCount_eq_toList_map_count tiling tile).symm

theorem czReducedBoundary_has_factorization
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    HasConwayLagariasWordFactorization
      (labeledEdgeWord (czReducedBoundaryWalk s r))
      (czReducedGeometricPeeling hs hr tiling).factors :=
  (czReducedGeometricPeeling hs hr tiling).hasFactorization

theorem czLiteralBoundary_has_factorization
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    HasConwayLagariasWordFactorization
      (classZeroLiteralBoundaryLabels s r)
      (czReducedGeometricPeeling hs hr tiling).factors := by
  have hreduce := reduceGeometricBacktracks_word_equivalent
    (classZeroLiteralBoundaryWalk s r)
  have hfactor := czReducedBoundary_has_factorization hs hr tiling
  have htrans := Relation.EqvGen.trans _ _ _ hreduce hfactor
  simpa [czReducedBoundaryWalk, classZeroLiteralBoundaryWalk_labels] using htrans

theorem czStoneAreaIdentity_int
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    2 * (offsetLiteralStoneCount tiling : ℤ) =
      (s : ℤ) ^ 2 + (r : ℤ) ^ 2 -
        (2 * (s : ℤ) * r + s + r) := by
  let factors := (czReducedGeometricPeeling hs hr tiling).factors
  have hfactorization := czLiteralBoundary_has_factorization hs hr tiling
  have hfactorIdentity :=
    boundary_identity_of_conwayLagarias_factorization hfactorization
  have houter := classZeroLiteralBoundary_identityWord s r
  have hsummary := hfactorIdentity.2.symm.trans houter.2
  have harea := congrArg ShadowSummary.areaNumerator hsummary
  have hfactor := shadowFactorArea_eq_stones factors
  have hcount : shadowFactorTileCount factors .stone =
      offsetLiteralStoneCount tiling := by
    change shadowFactorTileCount factors (d4ToShadowTile .stone) = _
    rw [shadowFactorTileCount_eq_factorProtoTileCount,
      (czReducedGeometricPeeling hs hr tiling).factorProtoTileCount_eq_placementCount,
      (czReducedGeometricPeeling_placements_perm hs hr tiling).map
        LiteralPlacement.tile |>.count_eq,
      czShadowPlacementFinset_tile_count]
    rfl
  rw [hcount] at hfactor
  rw [hfactor] at harea
  change 18 * (offsetLiteralStoneCount tiling : ℤ) =
    9 * ((s : ℤ) ^ 2 - 2 * (s : ℤ) * (r : ℤ) +
      (r : ℤ) ^ 2 - (s : ℤ) - (r : ℤ)) at harea
  nlinarith

theorem czStoneNumerator_nonnegative
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    2 * s * r + s + r ≤ s * s + r * r := by
  have harea := czStoneAreaIdentity_int hs hr tiling
  have hz : (2 * s * r + s + r : ℤ) ≤ s * s + r * r := by
    nlinarith [show (0 : ℤ) ≤ offsetLiteralStoneCount tiling by omega]
  exact_mod_cast hz

theorem twice_czLiteralStoneCount
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    2 * offsetLiteralStoneCount tiling =
      s * s + r * r - (2 * s * r + s + r) := by
  have harea := czStoneAreaIdentity_int hs hr tiling
  have hnonneg := czStoneNumerator_nonnegative hs hr tiling
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hnonneg]
  push_cast
  simpa [pow_two] using harea

theorem cz_stone_add_bone_eq_tiles
    {s r : ℕ} (tiling : CZLiteralTiling s r) :
    offsetLiteralStoneCount tiling + offsetBoneCount tiling = tiling.1.card := by
  classical
  exact Finset.filter_card_add_filter_neg_card_eq_card
    (s := tiling.1) (fun placement => placement.tile = .stone)

theorem cz_bone_count_kernelOnly
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    offsetBoneCount tiling = 3 * s * r := by
  have htiles := twice_cz_tiling_card hs hr tiling
  have hstones := twice_czLiteralStoneCount hs hr tiling
  have hpartition := cz_stone_add_bone_eq_tiles tiling
  have htotalBound : s + r ≤ s * s + r * r + 4 * s * r := by nlinarith
  have hstoneBound := czStoneNumerator_nonnegative hs hr tiling
  have htZ := congrArg (fun n : ℕ => (n : ℤ)) htiles
  have hsZ := congrArg (fun n : ℕ => (n : ℤ)) hstones
  have hpZ := congrArg (fun n : ℕ => (n : ℤ)) hpartition
  push_cast at htZ hsZ hpZ
  rw [Nat.cast_sub htotalBound] at htZ
  rw [Nat.cast_sub hstoneBound] at hsZ
  push_cast at htZ hsZ
  apply Nat.cast_injective (R := ℤ)
  push_cast
  nlinarith [htZ, hsZ, hpZ]

end FiniteDefects
