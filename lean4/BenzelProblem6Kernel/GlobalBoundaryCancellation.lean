import BenzelProblem6Kernel.TilingCellPermutation

/-!
# Global labeled-boundary cancellation for a literal tiling

The exact-cover permutation lets us compare two evaluations of the same list
of benzel cells.  Grouping the cells by placements cancels the two internal
edges of each trihex and leaves the XOR of literal placement boundaries;
forgetting that grouping leaves the canonical XOR of all benzel-cell
boundaries.
-/

namespace BenzelProblem6Kernel

open scoped symmDiff

theorem xorCellBoundaryList_append (left right : List Cell) :
    xorCellBoundaryList (left ++ right) =
      xorCellBoundaryList left ∆ xorCellBoundaryList right := by
  induction left with
  | nil =>
      apply Finset.ext
      intro edge
      simp [xorCellBoundaryList, Finset.mem_symmDiff]
  | cons cell rest ih =>
      simp only [List.cons_append, xorCellBoundaryList, ih]
      rw [symmDiff_assoc]

private theorem foldr_symmDiff_perm {Alpha Beta : Type*}
    [GeneralizedBooleanAlgebra Beta] (value : Alpha → Beta)
    {left right : List Alpha} (hperm : List.Perm left right) :
    left.foldr (fun item rest => value item ∆ rest) ⊥ =
      right.foldr (fun item rest => value item ∆ rest) ⊥ := by
  letI : LeftCommutative (fun item rest => value item ∆ rest) := ⟨by
    intro leftItem rightItem rest
    rw [← symmDiff_assoc,
      symmDiff_comm (value leftItem) (value rightItem),
      symmDiff_assoc]⟩
  exact hperm.foldr_eq ⊥

theorem xorCellBoundaryList_eq_foldr (cells : List Cell) :
    xorCellBoundaryList cells =
      cells.foldr (fun cell rest => cellBoundaryKeys cell ∆ rest) ∅ := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [xorCellBoundaryList, List.foldr]
      rw [ih]

theorem xorCellBoundaryList_perm {left right : List Cell}
    (hperm : List.Perm left right) :
    xorCellBoundaryList left = xorCellBoundaryList right := by
  rw [xorCellBoundaryList_eq_foldr, xorCellBoundaryList_eq_foldr]
  exact foldr_symmDiff_perm cellBoundaryKeys hperm

def xorPlacementBoundaryList {m : ℕ} :
    List (LiteralPlacement m) → Finset LabeledHexEdgeKey
  | [] => ∅
  | placement :: rest =>
      literalPlacementBoundaryKeys placement ∆
        xorPlacementBoundaryList rest

theorem xorCellBoundaryList_flatMap_placementCells {m : ℕ}
    (placements : List (LiteralPlacement m)) :
    xorCellBoundaryList
        (placements.flatMap LiteralPlacement.cells) =
      xorPlacementBoundaryList placements := by
  induction placements with
  | nil => rfl
  | cons placement rest ih =>
      simp only [List.flatMap_cons, xorPlacementBoundaryList]
      rw [xorCellBoundaryList_append,
        literalPlacementBoundaryKeys_eq_cells, ih]

noncomputable def literalTilingBoundaryKeys {m : ℕ}
    (tiling : LiteralTiling m) : Finset LabeledHexEdgeKey :=
  xorPlacementBoundaryList tiling.1.toList

theorem literalTilingBoundaryKeys_eq_flattenedCells {m : ℕ}
    (tiling : LiteralTiling m) :
    literalTilingBoundaryKeys tiling =
      xorCellBoundaryList (tilingCellList tiling) := by
  rw [literalTilingBoundaryKeys, tilingCellList,
    xorCellBoundaryList_flatMap_placementCells]

theorem literalTilingBoundaryKeys_eq_benzelCells {m : ℕ}
    (tiling : LiteralTiling m) :
    literalTilingBoundaryKeys tiling =
      xorCellBoundaryList (benzelCellValueList m) := by
  rw [literalTilingBoundaryKeys_eq_flattenedCells]
  exact xorCellBoundaryList_perm
    (tilingCellList_perm_benzelCells tiling)

end BenzelProblem6Kernel
