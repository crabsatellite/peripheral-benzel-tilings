import D4KernelOnly.GeneralShadowPlacement
import BenzelProblem6Kernel.OrientedTilingCellBoundary
import Mathlib.Data.List.Perm.Basic

/-! # Literal cell permutation and placement-boundary cancellation -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def offsetCellValueList (t d : ℕ) : List Cell :=
  ((Finset.univ : Finset (OffsetCell t d)).toList.map Subtype.val)

theorem mem_offsetTilingCellList_iff {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) (cell : Cell) :
    cell ∈ offsetTilingCellList tiling ↔
      inBenzel (t + 2) (offsetB t d) cell := by
  constructor
  · simp only [offsetTilingCellList, List.mem_flatMap, Finset.mem_toList]
    rintro ⟨placement, hplacement, hcell⟩
    exact placement.2 cell hcell
  · intro hcell
    let regionCell : OffsetCell t d := ⟨cell, hcell⟩
    obtain ⟨placement, hplacement, _⟩ := tiling.2 regionCell
    rw [offsetTilingCellList, List.mem_flatMap]
    exact ⟨placement, Finset.mem_toList.mpr hplacement.1, hplacement.2⟩

theorem mem_offsetCellValueList_iff (t d : ℕ) (cell : Cell) :
    cell ∈ offsetCellValueList t d ↔
      inBenzel (t + 2) (offsetB t d) cell := by
  simp [offsetCellValueList]

theorem offsetCellValueList_nodup (t d : ℕ) :
    (offsetCellValueList t d).Nodup :=
  (Finset.nodup_toList _).map Subtype.val_injective

theorem offsetTilingCellList_perm_cells {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    List.Perm (offsetTilingCellList tiling) (offsetCellValueList t d) := by
  apply (List.perm_ext_iff_of_nodup
    (offsetTilingCellList_nodup tiling)
    (offsetCellValueList_nodup t d)).mpr
  intro cell
  exact (mem_offsetTilingCellList_iff tiling cell).trans
    (mem_offsetCellValueList_iff t d cell).symm

theorem offsetShadowPlacementBoundaries_eq_cellBoundaries {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    SameOrientedBoundaryChain
      (literalPlacementBoundaryList (offsetShadowPlacementList tiling))
      (orientedCellBoundaryList (offsetCellValueList t d)) := by
  have hgrouped :=
    (orientedCellBoundaryList_flatMap_placements
      (offsetShadowPlacementList tiling)).symm
  have hflatten :
      (offsetShadowPlacementList tiling).flatMap
          BenzelProblem6Kernel.LiteralPlacement.cells =
        offsetTilingCellList tiling :=
    offsetShadowPlacementList_cells tiling
  have hcells : SameOrientedBoundaryChain
      (orientedCellBoundaryList
        ((offsetShadowPlacementList tiling).flatMap
          BenzelProblem6Kernel.LiteralPlacement.cells))
      (orientedCellBoundaryList (offsetCellValueList t d)) := by
    rw [hflatten]
    exact orientedCellBoundaryList_perm
      (offsetTilingCellList_perm_cells tiling)
  exact hgrouped.trans hcells

end FiniteDefects
