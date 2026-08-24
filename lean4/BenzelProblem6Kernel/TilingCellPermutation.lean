import BenzelProblem6Kernel.CanonicalBoundaryCancellation
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Flatten

/-!
# The flattened cells of a literal exact cover
-/

namespace BenzelProblem6Kernel

noncomputable def tilingCellList {m : ℕ} (tiling : LiteralTiling m) :
    List Cell :=
  tiling.1.toList.flatMap LiteralPlacement.cells

noncomputable def benzelCellValueList (m : ℕ) : List Cell :=
  ((Finset.univ : Finset (BenzelCell (m + 5))).toList.map Subtype.val)

theorem mem_tilingCellList_iff {m : ℕ} (tiling : LiteralTiling m)
    (cell : Cell) :
    cell ∈ tilingCellList tiling ↔ inPeripheralBenzel (m + 5) cell := by
  constructor
  · simp only [tilingCellList, List.mem_flatMap, Finset.mem_toList]
    rintro ⟨placement, hplacement, hcell⟩
    exact placement.2 cell hcell
  · intro hcell
    let regionCell : BenzelCell (m + 5) := ⟨cell, hcell⟩
    obtain ⟨placement, hplacement, _⟩ := tiling.2 regionCell
    rw [tilingCellList, List.mem_flatMap]
    exact ⟨placement, Finset.mem_toList.mpr hplacement.1, hplacement.2⟩

theorem mem_benzelCellValueList_iff {m : ℕ} (cell : Cell) :
    cell ∈ benzelCellValueList m ↔ inPeripheralBenzel (m + 5) cell := by
  simp [benzelCellValueList]

theorem tilingCellList_nodup {m : ℕ} (tiling : LiteralTiling m) :
    (tilingCellList tiling).Nodup := by
  rw [tilingCellList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact placementCellList_nodup placement.1
  · apply (Finset.nodup_toList tiling.1).pairwise_of_forall_ne
    intro left hleft right hright hne
    change List.Disjoint left.cells right.cells
    rw [List.disjoint_left]
    intro cell hcellLeft hcellRight
    let regionCell : BenzelCell (m + 5) :=
      ⟨cell, left.2 cell hcellLeft⟩
    obtain ⟨placement, hplacement, hunique⟩ := tiling.2 regionCell
    have hleftUnique : left = placement := hunique left ⟨
      Finset.mem_toList.mp hleft, hcellLeft⟩
    have hrightUnique : right = placement := hunique right ⟨
      Finset.mem_toList.mp hright, hcellRight⟩
    exact hne (hleftUnique.trans hrightUnique.symm)

theorem benzelCellValueList_nodup (m : ℕ) :
    (benzelCellValueList m).Nodup := by
  exact (Finset.nodup_toList _).map Subtype.val_injective

theorem tilingCellList_perm_benzelCells {m : ℕ} (tiling : LiteralTiling m) :
    List.Perm (tilingCellList tiling) (benzelCellValueList m) := by
  apply (List.perm_ext_iff_of_nodup
    (tilingCellList_nodup tiling) (benzelCellValueList_nodup m)).mpr
  intro cell
  exact (mem_tilingCellList_iff tiling cell).trans
    (mem_benzelCellValueList_iff cell).symm

end BenzelProblem6Kernel
