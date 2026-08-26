import D4KernelOnly.D4ConwayLagariasKernelConsumer
import BenzelProblem6Kernel.LiteralTilingCarrier

/-!
# Faithful embedding of d=4 placements into the shared boundary geometry

The ambient Problem 6 benzel at parameter `m` strictly contains the d=4
benzel.  This file uses that containment only to reuse the already checked
hex-edge and tile-boundary carrier.  It does not extend a d=4 tiling to a
Problem 6 tiling.
-/

namespace FiniteDefects

namespace P6

abbrev Cell := BenzelProblem6Kernel.Cell
abbrev LiteralPlacement := BenzelProblem6Kernel.LiteralPlacement

end P6

theorem d4_in_problem6_ambient (m : ℕ) (cell : Cell)
    (hcell : inBenzel (m + 4) (2 * m + 4) cell) :
    BenzelProblem6Kernel.inPeripheralBenzel (m + 5) cell := by
  dsimp [inBenzel] at hcell
  dsimp [BenzelProblem6Kernel.inPeripheralBenzel]
  omega

def d4ToShadowTile_injective : Function.Injective d4ToShadowTile := by
  intro left right h
  rcases left <;> rcases right <;> simp_all [d4ToShadowTile]

def d4ShadowPlacementCandidate {m : ℕ}
    (placement : D4LiteralPlacement m) :
    BenzelProblem6Kernel.PlacementCandidate m :=
  (d4ToShadowTile placement.tile,
    ⟨placement.base,
      d4_in_problem6_ambient m placement.base placement.1.2.2⟩)

theorem d4ShadowPlacementCandidate_cells {m : ℕ}
    (placement : D4LiteralPlacement m) :
    BenzelProblem6Kernel.placementCellList
        (d4ShadowPlacementCandidate placement) =
      placement.cells := by
  rcases placement with ⟨⟨tile, base⟩, inside⟩
  rcases tile with _ | _ | _ | _ <;>
    simp [d4ShadowPlacementCandidate,
      BenzelProblem6Kernel.placementCellList,
      BenzelProblem6Kernel.protoCells,
      BenzelProblem6Kernel.translateLocalCell,
      BenzelProblem6Kernel.c00, BenzelProblem6Kernel.c10,
      BenzelProblem6Kernel.c20, BenzelProblem6Kernel.c01,
      BenzelProblem6Kernel.c02, BenzelProblem6Kernel.c1m1,
      BenzelProblem6Kernel.c2m2,
      D4LiteralPlacement.cells, D4LiteralPlacement.base,
      d4PlacementCellList, D4LiteralPlacement.tile,
      protoCells, translateLocalCell,
      c00, c10, c20, c01, c02, c1m1, c2m2,
      d4ToShadowTile]

def d4ShadowPlacement {m : ℕ}
    (placement : D4LiteralPlacement m) :
    BenzelProblem6Kernel.LiteralPlacement m :=
  ⟨d4ShadowPlacementCandidate placement, by
    intro cell hcell
    apply d4_in_problem6_ambient m cell
    apply placement.2 cell
    change cell ∈ placement.cells
    rw [← d4ShadowPlacementCandidate_cells placement]
    exact hcell⟩

@[simp] theorem d4ShadowPlacement_tile {m : ℕ}
    (placement : D4LiteralPlacement m) :
    (d4ShadowPlacement placement).tile =
      d4ToShadowTile placement.tile := rfl

@[simp] theorem d4ShadowPlacement_base {m : ℕ}
    (placement : D4LiteralPlacement m) :
    (d4ShadowPlacement placement).base = placement.base := rfl

theorem d4ShadowPlacement_cells {m : ℕ}
    (placement : D4LiteralPlacement m) :
    (d4ShadowPlacement placement).cells = placement.cells :=
  d4ShadowPlacementCandidate_cells placement

theorem d4ShadowPlacement_injective {m : ℕ} :
    Function.Injective
      (d4ShadowPlacement : D4LiteralPlacement m →
        BenzelProblem6Kernel.LiteralPlacement m) := by
  intro left right h
  have htile : left.tile = right.tile := by
    apply d4ToShadowTile_injective
    simpa using congrArg BenzelProblem6Kernel.LiteralPlacement.tile h
  have hbase : left.base = right.base := by
    simpa using congrArg BenzelProblem6Kernel.LiteralPlacement.base h
  apply Subtype.ext
  apply Prod.ext htile
  apply Subtype.ext
  exact hbase

def d4ShadowPlacementEmbedding (m : ℕ) :
    D4LiteralPlacement m ↪ BenzelProblem6Kernel.LiteralPlacement m where
  toFun := d4ShadowPlacement
  inj' := d4ShadowPlacement_injective

noncomputable def d4ShadowPlacementFinset {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Finset (BenzelProblem6Kernel.LiteralPlacement m) :=
  tiling.1.map (d4ShadowPlacementEmbedding m)

noncomputable def d4TilingCellList {m : ℕ}
    (tiling : D4LiteralTiling m) : List Cell :=
  tiling.1.toList.flatMap D4LiteralPlacement.cells

theorem d4TilingCellList_nodup {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TilingCellList tiling).Nodup := by
  rw [d4TilingCellList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact d4PlacementCellList_nodup placement.1
  · apply (Finset.nodup_toList tiling.1).pairwise_of_forall_ne
    intro left hleft right hright hne
    change List.Disjoint left.cells right.cells
    rw [List.disjoint_left]
    intro cell hcellLeft hcellRight
    let regionCell : D4Cell m :=
      ⟨cell, left.2 cell hcellLeft⟩
    obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
    have hleftUnique : left = covering := hunique left
      ⟨Finset.mem_toList.mp hleft, hcellLeft⟩
    have hrightUnique : right = covering := hunique right
      ⟨Finset.mem_toList.mp hright, hcellRight⟩
    exact hne (hleftUnique.trans hrightUnique.symm)

noncomputable def d4ShadowPlacementList {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List (BenzelProblem6Kernel.LiteralPlacement m) :=
  tiling.1.toList.map d4ShadowPlacement

theorem d4ShadowPlacementList_cells {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ShadowPlacementList tiling).flatMap
        BenzelProblem6Kernel.LiteralPlacement.cells =
      d4TilingCellList tiling := by
  unfold d4ShadowPlacementList d4TilingCellList
  induction tiling.1.toList with
  | nil => rfl
  | cons placement rest ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [d4ShadowPlacement_cells, ih]

theorem d4ShadowPlacementList_cells_nodup {m : ℕ}
    (tiling : D4LiteralTiling m) :
    ((d4ShadowPlacementList tiling).flatMap
      BenzelProblem6Kernel.LiteralPlacement.cells).Nodup := by
  rw [d4ShadowPlacementList_cells]
  exact d4TilingCellList_nodup tiling

end FiniteDefects
