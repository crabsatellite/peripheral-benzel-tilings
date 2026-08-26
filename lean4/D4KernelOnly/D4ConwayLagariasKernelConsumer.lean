import D4KernelOnly.D4ShadowSymmetry
import BenzelProblem6Kernel.ConwayLagariasWordAlgebra

/-!
# Kernel consumer from a literal d=4 boundary factorization

All Conway--Lagarias algebra and the specialized outer-boundary area are
proved here.  The sole remaining producer is the geometric statement that the
ordered boundary of a literal exact cover factors into the ordered boundaries
of its actual placements with exact multiplicity.
-/

namespace FiniteDefects

def d4ToShadowTile : ProtoTile → BenzelProblem6Kernel.ProtoTile
  | .stone => .stone
  | .boneA => .boneA
  | .boneB => .boneB
  | .boneC => .boneC

def d4LiteralProtoTileCount {m : ℕ}
    (tiling : D4LiteralTiling m) (tile : ProtoTile) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = tile).card

theorem d4LiteralProtoTileCount_stone {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4LiteralProtoTileCount tiling .stone =
      d4KernelRightStoneCount tiling := rfl

def shadowFactorTileCount :
    List BenzelProblem6Kernel.ConwayLagariasWordFactor →
      BenzelProblem6Kernel.ProtoTile → ℕ
  | [], _tile => 0
  | factor :: rest, tile =>
      (if factor.tile = tile then 1 else 0) +
        shadowFactorTileCount rest tile

structure D4LiteralBoundaryFactorization {m : ℕ}
    (tiling : D4LiteralTiling m) where
  factors : List BenzelProblem6Kernel.ConwayLagariasWordFactor
  boundary_equivalent :
    BenzelProblem6Kernel.HasConwayLagariasWordFactorization
      (d4LiteralBoundaryLabels m) factors
  tile_count_exact :
    ∀ tile : ProtoTile,
      shadowFactorTileCount factors (d4ToShadowTile tile) =
        d4LiteralProtoTileCount tiling tile

theorem shadowFactorArea_eq_stones
    (factors : List BenzelProblem6Kernel.ConwayLagariasWordFactor) :
    BenzelProblem6Kernel.conwayLagariasFactorArea factors =
      18 * (shadowFactorTileCount factors .stone : ℤ) := by
  induction factors with
  | nil =>
      simp [BenzelProblem6Kernel.conwayLagariasFactorArea,
        shadowFactorTileCount]
  | cons factor rest ih =>
      rcases factor with ⟨tile, path, pathEven⟩
      cases tile
      all_goals
        simp [BenzelProblem6Kernel.conwayLagariasFactorArea,
          shadowFactorTileCount,
          BenzelProblem6Kernel.ConwayLagariasWordFactor.area,
          BenzelProblem6Kernel.protoTileShadowArea, ih]
      all_goals ring

theorem d4KernelRightStoneCount_of_boundaryFactorization {m : ℕ}
    (tiling : D4LiteralTiling m)
    (factorization : D4LiteralBoundaryFactorization tiling) :
    d4KernelRightStoneCount tiling = d4KernelStoneTarget m := by
  have hfactorIdentity :=
    BenzelProblem6Kernel.boundary_identity_of_conwayLagarias_factorization
      factorization.boundary_equivalent
  have houter := d4LiteralBoundary_identityWord m
  have hsummary := hfactorIdentity.2.symm.trans houter.2
  have harea := congrArg BenzelProblem6Kernel.ShadowSummary.areaNumerator
    hsummary
  have hfactor := shadowFactorArea_eq_stones factorization.factors
  have hcount := factorization.tile_count_exact .stone
  change shadowFactorTileCount factorization.factors .stone =
    d4KernelRightStoneCount tiling at hcount
  rw [hcount] at hfactor
  rw [hfactor] at harea
  change 18 * (d4KernelRightStoneCount tiling : ℤ) =
    18 * (d4KernelStoneTarget m : ℤ) at harea
  have hcast :
      (d4KernelRightStoneCount tiling : ℤ) =
        d4KernelStoneTarget m := by
    nlinarith
  exact_mod_cast hcast

def D4LiteralBoundaryFactorizationStatement : Prop :=
  ∀ (m : ℕ) (tiling : D4LiteralTiling m),
    Nonempty (D4LiteralBoundaryFactorization tiling)

theorem d4KernelStoneStatement_of_boundaryFactorization
    (hfactor : D4LiteralBoundaryFactorizationStatement) :
    D4KernelStoneStatement := by
  intro m tiling
  exact d4KernelRightStoneCount_of_boundaryFactorization tiling
    (hfactor m tiling).some

end FiniteDefects
