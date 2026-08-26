import FiniteDefects.OwnerDomainHierarchy
import FiniteDefects.LiteralTiles
import Mathlib.Data.Fintype.Powerset

/-! # Literal exact-cover carrier on the d=4 diagonal -/

namespace FiniteDefects

instance inBenzelDecidable (a b : ℕ) (cell : Cell) :
    Decidable (inBenzel a b cell) := by
  unfold inBenzel
  infer_instance

instance microLabelFintype : Fintype MicroLabel :=
  Fintype.ofList [.zero, .one, .two] (by
    intro label
    rcases label with _ | _ | _ <;> simp)

instance protoTileFintype : Fintype ProtoTile :=
  Fintype.ofList [.stone, .boneA, .boneB, .boneC] (by
    intro tile
    rcases tile with _ | _ | _ | _ <;> simp)

abbrev D4Cell (m : ℕ) :=
  {cell : Cell // inBenzel (m + 4) (2 * m + 4) cell}

abbrev D4OwnerLabelPair (m : ℕ) :=
  SimplexPoint (m + 2) × MicroLabel

def IsPresentD4OwnerLabel (m : ℕ) (pair : D4OwnerLabelPair m) : Prop :=
  inBenzel (m + 4) (2 * m + 4) (ownerCell pair.1 pair.2)

abbrev PresentD4OwnerLabel (m : ℕ) :=
  {pair : D4OwnerLabelPair m // IsPresentD4OwnerLabel m pair}

noncomputable instance presentD4OwnerLabelFintype (m : ℕ) :
    Fintype (PresentD4OwnerLabel m) :=
  Fintype.ofFinite (PresentD4OwnerLabel m)

def d4OwnerCellMap (m : ℕ) : PresentD4OwnerLabel m → D4Cell m :=
  fun pair => ⟨ownerCell pair.1.1 pair.1.2, pair.2⟩

theorem d4OwnerCellMap_injective (m : ℕ) :
    Function.Injective (d4OwnerCellMap m) := by
  rintro ⟨⟨p, label⟩, hpresent⟩ ⟨⟨p', label'⟩, hpresent'⟩ heq
  have hcell : ownerCell p label = ownerCell p' label' :=
    congrArg Subtype.val heq
  obtain ⟨hp, hlabel⟩ := owner_representation_unique
    (ownerCell p label) p p' label label' rfl hcell.symm
  apply Subtype.ext
  exact Prod.ext hp hlabel

theorem d4OwnerCellMap_surjective (m : ℕ) :
    Function.Surjective (d4OwnerCellMap m) := by
  intro cell
  obtain ⟨p, label, hcell⟩ :=
    benzel_cell_has_owner (m + 2) (2 * m + 4) cell.1 (by
      simpa only [show m + 2 + 2 = m + 4 by omega] using cell.2)
  let pair : PresentD4OwnerLabel m :=
    ⟨(p, label), by
      unfold IsPresentD4OwnerLabel
      simpa [hcell] using cell.2⟩
  refine ⟨pair, ?_⟩
  apply Subtype.ext
  exact hcell

noncomputable def d4OwnerCellEquiv (m : ℕ) :
    PresentD4OwnerLabel m ≃ D4Cell m :=
  Equiv.ofBijective (d4OwnerCellMap m)
    ⟨d4OwnerCellMap_injective m, d4OwnerCellMap_surjective m⟩

noncomputable instance d4CellFintype (m : ℕ) : Fintype (D4Cell m) :=
  Fintype.ofEquiv (PresentD4OwnerLabel m) (d4OwnerCellEquiv m)

abbrev D4PlacementCandidate (m : ℕ) := ProtoTile × D4Cell m

def d4PlacementCellList {m : ℕ}
    (candidate : D4PlacementCandidate m) : List Cell :=
  (protoCells candidate.1).map (translateLocalCell candidate.2.1)

def D4PlacementInside {m : ℕ} (candidate : D4PlacementCandidate m) : Prop :=
  ∀ cell ∈ d4PlacementCellList candidate,
    inBenzel (m + 4) (2 * m + 4) cell

instance d4PlacementInsideDecidable {m : ℕ}
    (candidate : D4PlacementCandidate m) :
    Decidable (D4PlacementInside candidate) := by
  unfold D4PlacementInside
  infer_instance

abbrev D4LiteralPlacement (m : ℕ) :=
  {candidate : D4PlacementCandidate m // D4PlacementInside candidate}

def D4LiteralPlacement.tile {m : ℕ}
    (placement : D4LiteralPlacement m) : ProtoTile := placement.1.1

def D4LiteralPlacement.base {m : ℕ}
    (placement : D4LiteralPlacement m) : Cell := placement.1.2.1

def D4LiteralPlacement.cells {m : ℕ}
    (placement : D4LiteralPlacement m) : List Cell :=
  d4PlacementCellList placement.1

def D4PlacementCovers {m : ℕ} (placement : D4LiteralPlacement m)
    (cell : D4Cell m) : Prop := cell.1 ∈ placement.cells

instance d4PlacementCoversDecidable {m : ℕ}
    (placement : D4LiteralPlacement m) (cell : D4Cell m) :
    Decidable (D4PlacementCovers placement cell) := by
  unfold D4PlacementCovers
  infer_instance

def IsD4LiteralTiling {m : ℕ}
    (chosen : Finset (D4LiteralPlacement m)) : Prop :=
  ∀ cell : D4Cell m,
    ∃! placement : D4LiteralPlacement m,
      placement ∈ chosen ∧ D4PlacementCovers placement cell

noncomputable instance isD4LiteralTilingDecidable {m : ℕ}
    (chosen : Finset (D4LiteralPlacement m)) :
    Decidable (IsD4LiteralTiling chosen) := by
  classical
  unfold IsD4LiteralTiling
  infer_instance

abbrev D4LiteralTiling (m : ℕ) :=
  {chosen : Finset (D4LiteralPlacement m) // IsD4LiteralTiling chosen}

theorem protoCells_length (tile : ProtoTile) : (protoCells tile).length = 3 := by
  rcases tile with _ | _ | _ | _ <;> rfl

theorem d4PlacementCellList_length {m : ℕ}
    (candidate : D4PlacementCandidate m) :
    (d4PlacementCellList candidate).length = 3 := by
  simp [d4PlacementCellList, protoCells_length]

theorem d4PlacementCellList_nodup {m : ℕ}
    (candidate : D4PlacementCandidate m) :
    (d4PlacementCellList candidate).Nodup := by
  rcases candidate with ⟨tile, base⟩
  rcases tile with _ | _ | _ | _ <;>
    simp [d4PlacementCellList, protoCells, translateLocalCell,
      c00, c10, c20, c01, c02, c1m1, c2m2]
  all_goals constructor <;> intro h
  all_goals
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    simp at hfst hsnd

end FiniteDefects
