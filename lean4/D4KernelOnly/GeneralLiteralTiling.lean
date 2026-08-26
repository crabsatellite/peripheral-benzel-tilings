import FiniteDefects.D4LiteralTiling
import Mathlib.Data.Fintype.Powerset

/-! # Literal exact-cover carriers for every fixed offset

The first parameter is `t = a - 2`; the second is `d = 2a - b`.  Consequently
the literal region is `B(t + 2, 2 * t + 4 - d)`.
-/

namespace FiniteDefects

def offsetB (t d : ℕ) : ℕ := 2 * t + 4 - d

abbrev OffsetCell (t d : ℕ) :=
  {cell : Cell // inBenzel (t + 2) (offsetB t d) cell}

abbrev OffsetOwnerLabelPair (t : ℕ) := SimplexPoint t × MicroLabel

def IsPresentOffsetOwnerLabel (t d : ℕ)
    (pair : OffsetOwnerLabelPair t) : Prop :=
  inBenzel (t + 2) (offsetB t d) (ownerCell pair.1 pair.2)

abbrev PresentOffsetOwnerLabel (t d : ℕ) :=
  {pair : OffsetOwnerLabelPair t // IsPresentOffsetOwnerLabel t d pair}

noncomputable instance presentOffsetOwnerLabelFintype (t d : ℕ) :
    Fintype (PresentOffsetOwnerLabel t d) :=
  Fintype.ofFinite (PresentOffsetOwnerLabel t d)

def offsetOwnerCellMap (t d : ℕ) :
    PresentOffsetOwnerLabel t d → OffsetCell t d :=
  fun pair => ⟨ownerCell pair.1.1 pair.1.2, pair.2⟩

theorem offsetOwnerCellMap_injective (t d : ℕ) :
    Function.Injective (offsetOwnerCellMap t d) := by
  rintro ⟨⟨p, label⟩, hpresent⟩ ⟨⟨p', label'⟩, hpresent'⟩ heq
  have hcell : ownerCell p label = ownerCell p' label' :=
    congrArg Subtype.val heq
  obtain ⟨hp, hlabel⟩ := owner_representation_unique
    (ownerCell p label) p p' label label' rfl hcell.symm
  apply Subtype.ext
  exact Prod.ext hp hlabel

theorem offsetOwnerCellMap_surjective (t d : ℕ) :
    Function.Surjective (offsetOwnerCellMap t d) := by
  intro cell
  obtain ⟨p, label, hcell⟩ :=
    benzel_cell_has_owner t (offsetB t d) cell.1 cell.2
  let pair : PresentOffsetOwnerLabel t d :=
    ⟨(p, label), by
      unfold IsPresentOffsetOwnerLabel
      simpa [hcell] using cell.2⟩
  refine ⟨pair, ?_⟩
  apply Subtype.ext
  exact hcell

noncomputable def offsetOwnerCellEquiv (t d : ℕ) :
    PresentOffsetOwnerLabel t d ≃ OffsetCell t d :=
  Equiv.ofBijective (offsetOwnerCellMap t d)
    ⟨offsetOwnerCellMap_injective t d, offsetOwnerCellMap_surjective t d⟩

noncomputable instance offsetCellFintype (t d : ℕ) :
    Fintype (OffsetCell t d) :=
  Fintype.ofEquiv (PresentOffsetOwnerLabel t d) (offsetOwnerCellEquiv t d)

abbrev OffsetPlacementCandidate (t d : ℕ) := ProtoTile × OffsetCell t d

def offsetPlacementCellList {t d : ℕ}
    (candidate : OffsetPlacementCandidate t d) : List Cell :=
  (protoCells candidate.1).map (translateLocalCell candidate.2.1)

def OffsetPlacementInside {t d : ℕ}
    (candidate : OffsetPlacementCandidate t d) : Prop :=
  ∀ cell ∈ offsetPlacementCellList candidate,
    inBenzel (t + 2) (offsetB t d) cell

instance offsetPlacementInsideDecidable {t d : ℕ}
    (candidate : OffsetPlacementCandidate t d) :
    Decidable (OffsetPlacementInside candidate) := by
  unfold OffsetPlacementInside
  infer_instance

abbrev OffsetLiteralPlacement (t d : ℕ) :=
  {candidate : OffsetPlacementCandidate t d // OffsetPlacementInside candidate}

def OffsetLiteralPlacement.tile {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) : ProtoTile := placement.1.1

def OffsetLiteralPlacement.base {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) : Cell := placement.1.2.1

def OffsetLiteralPlacement.cells {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) : List Cell :=
  offsetPlacementCellList placement.1

def OffsetPlacementCovers {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) (cell : OffsetCell t d) : Prop :=
  cell.1 ∈ placement.cells

instance offsetPlacementCoversDecidable {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) (cell : OffsetCell t d) :
    Decidable (OffsetPlacementCovers placement cell) := by
  unfold OffsetPlacementCovers
  infer_instance

def IsOffsetLiteralTiling {t d : ℕ}
    (chosen : Finset (OffsetLiteralPlacement t d)) : Prop :=
  ∀ cell : OffsetCell t d,
    ∃! placement : OffsetLiteralPlacement t d,
      placement ∈ chosen ∧ OffsetPlacementCovers placement cell

noncomputable instance isOffsetLiteralTilingDecidable {t d : ℕ}
    (chosen : Finset (OffsetLiteralPlacement t d)) :
    Decidable (IsOffsetLiteralTiling chosen) := by
  classical
  unfold IsOffsetLiteralTiling
  infer_instance

abbrev OffsetLiteralTiling (t d : ℕ) :=
  {chosen : Finset (OffsetLiteralPlacement t d) // IsOffsetLiteralTiling chosen}

theorem offsetPlacementCellList_length {t d : ℕ}
    (candidate : OffsetPlacementCandidate t d) :
    (offsetPlacementCellList candidate).length = 3 := by
  simp [offsetPlacementCellList, FiniteDefects.protoCells_length]

theorem offsetPlacementCellList_nodup {t d : ℕ}
    (candidate : OffsetPlacementCandidate t d) :
    (offsetPlacementCellList candidate).Nodup := by
  rcases candidate with ⟨tile, base⟩
  rcases tile with _ | _ | _ | _ <;>
    simp [offsetPlacementCellList, protoCells, translateLocalCell,
      c00, c10, c20, c01, c02, c1m1, c2m2]
  all_goals constructor <;> intro h
  all_goals
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    simp at hfst hsnd

end FiniteDefects
