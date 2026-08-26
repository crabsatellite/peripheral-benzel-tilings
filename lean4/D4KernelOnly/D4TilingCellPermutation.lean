import D4KernelOnly.D4ShadowPlacement
import Mathlib.Data.List.Perm.Basic

/-! # The flattened d=4 tiling cells are exactly the benzel cells -/

namespace FiniteDefects

noncomputable def d4CellValueList (m : ℕ) : List Cell :=
  ((Finset.univ : Finset (D4Cell m)).toList.map Subtype.val)

theorem mem_d4TilingCellList_iff {m : ℕ}
    (tiling : D4LiteralTiling m) (cell : Cell) :
    cell ∈ d4TilingCellList tiling ↔
      inBenzel (m + 4) (2 * m + 4) cell := by
  constructor
  · simp only [d4TilingCellList, List.mem_flatMap,
      Finset.mem_toList]
    rintro ⟨placement, hplacement, hcell⟩
    exact placement.2 cell hcell
  · intro hcell
    let regionCell : D4Cell m := ⟨cell, hcell⟩
    obtain ⟨placement, hplacement, _⟩ := tiling.2 regionCell
    rw [d4TilingCellList, List.mem_flatMap]
    exact ⟨placement, Finset.mem_toList.mpr hplacement.1,
      hplacement.2⟩

theorem mem_d4CellValueList_iff (m : ℕ) (cell : Cell) :
    cell ∈ d4CellValueList m ↔
      inBenzel (m + 4) (2 * m + 4) cell := by
  simp [d4CellValueList]

theorem d4CellValueList_nodup (m : ℕ) :
    (d4CellValueList m).Nodup := by
  exact (Finset.nodup_toList _).map Subtype.val_injective

theorem d4TilingCellList_perm_d4Cells {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List.Perm (d4TilingCellList tiling) (d4CellValueList m) := by
  apply (List.perm_ext_iff_of_nodup
    (d4TilingCellList_nodup tiling) (d4CellValueList_nodup m)).mpr
  intro cell
  exact (mem_d4TilingCellList_iff tiling cell).trans
    (mem_d4CellValueList_iff m cell).symm

end FiniteDefects
