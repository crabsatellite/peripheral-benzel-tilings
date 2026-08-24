import BenzelProblem6Kernel.TilingComplexVerticesGlobal
import BenzelProblem6Kernel.LiteralTilingTerminalReversePairs
import BenzelProblem6Kernel.PeripheralIncidenceLength

/-! # Exact edge counts of the tiling complex and terminal contour -/

namespace BenzelProblem6Kernel

theorem literalPrototypeBoundary_length (tile : ProtoTile) (base : Cell) :
    (literalPrototypeBoundary tile base).length =
      if tile = .stone then 12 else 14 := by
  cases tile <;> rfl

theorem literalPlacementBoundary_length {m : ℕ}
    (placement : LiteralPlacement m) :
    (literalPlacementBoundary placement).length =
      if placement.tile = .stone then 12 else 14 :=
  literalPrototypeBoundary_length placement.tile placement.base

def listStoneCount {m : ℕ}
    (placements : List (LiteralPlacement m)) : ℕ :=
  (placements.filter fun placement => placement.tile = .stone).length

def listBoneCount {m : ℕ}
    (placements : List (LiteralPlacement m)) : ℕ :=
  (placements.filter fun placement => placement.tile ≠ .stone).length

theorem reverseLiteralPlacementBoundaryList_length {m : ℕ}
    (placements : List (LiteralPlacement m)) :
    (reverseLiteralPlacementBoundaryList placements).length =
      12 * listStoneCount placements + 14 * listBoneCount placements := by
  induction placements with
  | nil => rfl
  | cons placement rest ih =>
      change (reverseReorientedEdges
        (literalPlacementBoundary placement) ++
          reverseLiteralPlacementBoundaryList rest).length = _
      rw [List.length_append, ih,
        reverseReorientedEdges, List.length_map,
        List.length_reverse, literalPlacementBoundary_length]
      by_cases hstone : placement.tile = .stone <;>
        simp [listStoneCount, listBoneCount, hstone] <;> omega

theorem length_filter_toList_bool {Alpha : Type*}
    [DecidableEq Alpha] (items : Finset Alpha) (p : Alpha → Bool) :
    (items.toList.filter p).length =
      (items.filter fun item => p item = true).card := by
  have hperm : List.Perm (items.toList.filter p)
      (items.filter fun item => p item = true).toList := by
    apply (List.perm_ext_iff_of_nodup
      (Finset.nodup_toList items |>.filter p)
      (Finset.nodup_toList _)).mpr
    intro item
    simp
  simpa [Finset.length_toList] using hperm.length_eq

theorem listStoneCount_toList {m : ℕ} (tiling : LiteralTiling m) :
    listStoneCount tiling.1.toList = rightStoneCount tiling := by
  simpa [listStoneCount, rightStoneCount] using
    length_filter_toList_bool tiling.1
      (fun placement => placement.tile = .stone)

theorem listBoneCount_toList {m : ℕ} (tiling : LiteralTiling m) :
    listBoneCount tiling.1.toList = boneCount tiling := by
  simpa [listBoneCount, boneCount, Bool.not_eq_true] using
    length_filter_toList_bool tiling.1
      (fun placement => placement.tile ≠ .stone)

theorem reverseTilingBoundaryList_length {m : ℕ}
    (tiling : LiteralTiling m) :
    (reverseLiteralPlacementBoundaryList tiling.1.toList).length =
      12 * rightStoneCount tiling + 14 * boneCount tiling := by
  rw [reverseLiteralPlacementBoundaryList_length,
    listStoneCount_toList, listBoneCount_toList]

theorem literalTilingComplexDirectedEdges_length {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalTilingComplexDirectedEdges tiling).length =
      12 * m + 42 +
        (12 * rightStoneCount tiling + 14 * boneCount tiling) := by
  rw [literalTilingComplexDirectedEdges, List.length_append,
    literalReducedPeripheralBoundary_length,
    reverseTilingBoundaryList_length]

theorem selectedEdgePair_length (edge : LabeledHexEdge) :
    (selectedEdgePair edge).length = 2 := rfl

theorem RightmostPeelingSkeleton.selectedEdgePairs_length {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    skeleton.selectedEdgePairs.length = 2 * placements.card := by
  induction skeleton with
  | done => rfl
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      rw [RightmostPeelingSkeleton.selectedEdgePairs,
        List.length_append, selectedEdgePair_length, ih,
        Finset.card_erase_of_mem placement_mem]
      have hpositive : 0 < placements.card :=
        Finset.card_pos.mpr ⟨splice.placement, placement_mem⟩
      omega

theorem literalTilingRightmostTerminal_length {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalTilingRightmostTerminal tiling).edges.length =
      12 * m + 42 +
        (10 * rightStoneCount tiling + 12 * boneCount tiling) := by
  have hperm := literalTilingTerminal_edgeAccounting_perm tiling
  have hlength := hperm.length_eq
  rw [List.length_append,
    literalTilingComplexDirectedEdges_length,
    RightmostPeelingSkeleton.selectedEdgePairs_length] at hlength
  have hpartition := rightStoneCount_add_boneCount tiling
  omega

theorem terminal_length_add_two_eq_twice_boundary_vertices {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalTilingRightmostTerminal tiling).edges.length + 2 =
      2 * (tilingBoundaryVertexFinset tiling).card := by
  have hterminal := literalTilingRightmostTerminal_length tiling
  have hvertices := card_tilingBoundaryVertexFinset tiling
  have hfull := twice_card_benzelHexVertex m
  have hpartition := rightStoneCount_add_boneCount tiling
  have htiles := literal_tiling_card tiling
  obtain ⟨half, hproduct⟩ := two_dvd_tile_product m
  rw [hproduct] at htiles
  simp at htiles
  nlinarith

end BenzelProblem6Kernel
