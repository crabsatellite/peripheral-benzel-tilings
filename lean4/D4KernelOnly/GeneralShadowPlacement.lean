import D4KernelOnly.GeneralLiteralTiling
import D4KernelOnly.D4ConwayLagariasKernelConsumer
import BenzelProblem6Kernel.LiteralTilingCarrier

/-! # Embedding arbitrary-offset placements into the shared edge geometry -/

namespace FiniteDefects

theorem offset_in_problem6_ambient (t d : ℕ) (cell : Cell)
    (hcell : inBenzel (t + 2) (offsetB t d) cell) :
    BenzelProblem6Kernel.inPeripheralBenzel (t + 5) cell := by
  dsimp [inBenzel] at hcell
  dsimp [offsetB] at hcell
  dsimp [BenzelProblem6Kernel.inPeripheralBenzel]
  omega

def offsetShadowPlacementCandidate {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    BenzelProblem6Kernel.PlacementCandidate t :=
  (d4ToShadowTile placement.tile,
    ⟨placement.base,
      offset_in_problem6_ambient t d placement.base placement.1.2.2⟩)

theorem offsetShadowPlacementCandidate_cells {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    BenzelProblem6Kernel.placementCellList
        (offsetShadowPlacementCandidate placement) = placement.cells := by
  rcases placement with ⟨⟨tile, base⟩, inside⟩
  rcases tile with _ | _ | _ | _ <;>
    simp [offsetShadowPlacementCandidate,
      BenzelProblem6Kernel.placementCellList,
      BenzelProblem6Kernel.protoCells,
      BenzelProblem6Kernel.translateLocalCell,
      BenzelProblem6Kernel.c00, BenzelProblem6Kernel.c10,
      BenzelProblem6Kernel.c20, BenzelProblem6Kernel.c01,
      BenzelProblem6Kernel.c02, BenzelProblem6Kernel.c1m1,
      BenzelProblem6Kernel.c2m2,
      OffsetLiteralPlacement.cells, OffsetLiteralPlacement.base,
      offsetPlacementCellList, OffsetLiteralPlacement.tile,
      protoCells, translateLocalCell,
      c00, c10, c20, c01, c02, c1m1, c2m2,
      d4ToShadowTile]

def offsetShadowPlacement {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    BenzelProblem6Kernel.LiteralPlacement t :=
  ⟨offsetShadowPlacementCandidate placement, by
    intro cell hcell
    apply offset_in_problem6_ambient t d cell
    apply placement.2 cell
    change cell ∈ placement.cells
    rw [← offsetShadowPlacementCandidate_cells placement]
    exact hcell⟩

@[simp] theorem offsetShadowPlacement_tile {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    (offsetShadowPlacement placement).tile =
      d4ToShadowTile placement.tile := rfl

@[simp] theorem offsetShadowPlacement_base {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    (offsetShadowPlacement placement).base = placement.base := rfl

theorem offsetShadowPlacement_cells {t d : ℕ}
    (placement : OffsetLiteralPlacement t d) :
    (offsetShadowPlacement placement).cells = placement.cells :=
  offsetShadowPlacementCandidate_cells placement

theorem generalToShadowTile_injective : Function.Injective d4ToShadowTile := by
  intro left right h
  rcases left <;> rcases right <;> simp_all [d4ToShadowTile]

theorem offsetShadowPlacement_injective {t d : ℕ} :
    Function.Injective
      (offsetShadowPlacement : OffsetLiteralPlacement t d →
        BenzelProblem6Kernel.LiteralPlacement t) := by
  intro left right h
  have htile : left.tile = right.tile := by
    apply generalToShadowTile_injective
    simpa using congrArg BenzelProblem6Kernel.LiteralPlacement.tile h
  have hbase : left.base = right.base := by
    simpa using congrArg BenzelProblem6Kernel.LiteralPlacement.base h
  apply Subtype.ext
  apply Prod.ext htile
  apply Subtype.ext
  exact hbase

def offsetShadowPlacementEmbedding (t d : ℕ) :
    OffsetLiteralPlacement t d ↪ BenzelProblem6Kernel.LiteralPlacement t where
  toFun := offsetShadowPlacement
  inj' := offsetShadowPlacement_injective

noncomputable def offsetShadowPlacementFinset {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    Finset (BenzelProblem6Kernel.LiteralPlacement t) :=
  tiling.1.map (offsetShadowPlacementEmbedding t d)

noncomputable def offsetTilingCellList {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) : List Cell :=
  tiling.1.toList.flatMap OffsetLiteralPlacement.cells

theorem offsetTilingCellList_nodup {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    (offsetTilingCellList tiling).Nodup := by
  rw [offsetTilingCellList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact offsetPlacementCellList_nodup placement.1
  · apply (Finset.nodup_toList tiling.1).pairwise_of_forall_ne
    intro left hleft right hright hne
    change List.Disjoint left.cells right.cells
    rw [List.disjoint_left]
    intro cell hcellLeft hcellRight
    let regionCell : OffsetCell t d :=
      ⟨cell, left.2 cell hcellLeft⟩
    obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
    have hleftUnique : left = covering := hunique left
      ⟨Finset.mem_toList.mp hleft, hcellLeft⟩
    have hrightUnique : right = covering := hunique right
      ⟨Finset.mem_toList.mp hright, hcellRight⟩
    exact hne (hleftUnique.trans hrightUnique.symm)

noncomputable def offsetShadowPlacementList {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    List (BenzelProblem6Kernel.LiteralPlacement t) :=
  tiling.1.toList.map offsetShadowPlacement

theorem offsetShadowPlacementList_cells {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    (offsetShadowPlacementList tiling).flatMap
        BenzelProblem6Kernel.LiteralPlacement.cells =
      offsetTilingCellList tiling := by
  unfold offsetShadowPlacementList offsetTilingCellList
  induction tiling.1.toList with
  | nil => rfl
  | cons placement rest ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [offsetShadowPlacement_cells, ih]

theorem offsetShadowPlacementList_cells_nodup {t d : ℕ}
    (tiling : OffsetLiteralTiling t d) :
    ((offsetShadowPlacementList tiling).flatMap
      BenzelProblem6Kernel.LiteralPlacement.cells).Nodup := by
  rw [offsetShadowPlacementList_cells]
  exact offsetTilingCellList_nodup tiling

theorem mem_offsetShadowPlacementFinset_iff {t d : ℕ}
    (tiling : OffsetLiteralTiling t d)
    (placement : BenzelProblem6Kernel.LiteralPlacement t) :
    placement ∈ offsetShadowPlacementFinset tiling ↔
      ∃ source ∈ tiling.1, offsetShadowPlacement source = placement := by
  simp [offsetShadowPlacementFinset, offsetShadowPlacementEmbedding]

end FiniteDefects
