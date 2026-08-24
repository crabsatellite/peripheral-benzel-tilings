import BenzelProblem6Kernel.BenzelArea
import BenzelProblem6Kernel.LiteralTileEnergy
import Mathlib.Data.Fintype.Powerset

/-!
# Literal type-103 tiling carrier
-/

namespace BenzelProblem6Kernel

instance protoTileFintype : Fintype ProtoTile :=
  Fintype.ofList [.stone, .boneA, .boneB, .boneC] (by
    intro tile
    rcases tile with _ | _ | _ | _ <;> simp)

noncomputable instance peripheralBenzelCellFintype (m : ℕ) :
    Fintype (BenzelCell (m + 5)) :=
  benzelCellFintypeOf (by omega)

def translateLocalCell (base : Cell) (offset : LocalCell) : Cell :=
  (base.1 + offset.dx, base.2 + offset.dy)

abbrev PlacementCandidate (m : ℕ) :=
  ProtoTile × BenzelCell (m + 5)

def placementCellList {m : ℕ} (candidate : PlacementCandidate m) : List Cell :=
  (protoCells candidate.1).map (translateLocalCell candidate.2.1)

def PlacementInside {m : ℕ} (candidate : PlacementCandidate m) : Prop :=
  ∀ cell ∈ placementCellList candidate,
    inPeripheralBenzel (m + 5) cell

instance placementInsideDecidable {m : ℕ} (candidate : PlacementCandidate m) :
    Decidable (PlacementInside candidate) := by
  unfold PlacementInside
  infer_instance

abbrev LiteralPlacement (m : ℕ) :=
  {candidate : PlacementCandidate m // PlacementInside candidate}

def LiteralPlacement.tile {m : ℕ} (placement : LiteralPlacement m) : ProtoTile :=
  placement.1.1

def LiteralPlacement.base {m : ℕ} (placement : LiteralPlacement m) : Cell :=
  placement.1.2.1

def LiteralPlacement.cells {m : ℕ} (placement : LiteralPlacement m) : List Cell :=
  placementCellList placement.1

def PlacementCovers {m : ℕ} (placement : LiteralPlacement m)
    (cell : BenzelCell (m + 5)) : Prop :=
  cell.1 ∈ placement.cells

instance placementCoversDecidable {m : ℕ} (placement : LiteralPlacement m)
    (cell : BenzelCell (m + 5)) : Decidable (PlacementCovers placement cell) := by
  unfold PlacementCovers
  infer_instance

def IsLiteralTiling {m : ℕ} (chosen : Finset (LiteralPlacement m)) : Prop :=
  ∀ cell : BenzelCell (m + 5),
    ∃! placement : LiteralPlacement m,
      placement ∈ chosen ∧ PlacementCovers placement cell

noncomputable instance isLiteralTilingDecidable {m : ℕ}
    (chosen : Finset (LiteralPlacement m)) : Decidable (IsLiteralTiling chosen) := by
  classical
  unfold IsLiteralTiling
  infer_instance

abbrev LiteralTiling (m : ℕ) :=
  {chosen : Finset (LiteralPlacement m) // IsLiteralTiling chosen}

noncomputable def type103TilingCount (n : ℕ) : ℕ :=
  if 5 ≤ n then
    @Fintype.card (LiteralTiling (n - 5)) inferInstance
  else 0

theorem protoCells_length (tile : ProtoTile) :
    (protoCells tile).length = 3 := by
  rcases tile with _ | _ | _ | _ <;> rfl

theorem placementCellList_length {m : ℕ} (candidate : PlacementCandidate m) :
    (placementCellList candidate).length = 3 := by
  simp [placementCellList, protoCells_length]

theorem placementCellList_nodup {m : ℕ} (candidate : PlacementCandidate m) :
    (placementCellList candidate).Nodup := by
  rcases candidate with ⟨tile, base⟩
  rcases tile with _ | _ | _ | _ <;>
    simp [placementCellList, protoCells, translateLocalCell,
      c00, c10, c20, c01, c02, c1m1, c2m2]
  all_goals constructor <;> intro h
  all_goals
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    simp at hfst hsnd

theorem type103TilingCount_add_five (m : ℕ) :
    type103TilingCount (m + 5) = Fintype.card (LiteralTiling m) := by
  simp [type103TilingCount]

end BenzelProblem6Kernel
