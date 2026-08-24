import BenzelProblem6Kernel.ConwayLagariasWordAlgebra

/-!
# Exact boundary-factorization target for a literal tiling

The structure records the geometric factorization statement: the peripheral
boundary is a product of even-basepoint conjugates, with exactly one factor for
every literal placement of each prototile class.  All algebra from such a
factorization to the Conway--Lagarias stone count is premise-free below.
-/

namespace BenzelProblem6Kernel

def factorProtoTileCount :
    List ConwayLagariasWordFactor → ProtoTile → ℕ
  | [], _tile => 0
  | factor :: rest, tile =>
      (if factor.tile = tile then 1 else 0) +
        factorProtoTileCount rest tile

def literalProtoTileCount {m : ℕ}
    (tiling : LiteralTiling m) (tile : ProtoTile) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = tile).card

theorem literalProtoTileCount_stone {m : ℕ} (tiling : LiteralTiling m) :
    literalProtoTileCount tiling .stone = rightStoneCount tiling := rfl

theorem conwayLagariasFactorArea_eq_stones
    (factors : List ConwayLagariasWordFactor) :
    conwayLagariasFactorArea factors =
      18 * (factorProtoTileCount factors .stone : ℤ) := by
  induction factors with
  | nil => simp [conwayLagariasFactorArea, factorProtoTileCount]
  | cons factor rest ih =>
      rcases factor with ⟨tile, path, path_even⟩
      cases tile
      all_goals simp [conwayLagariasFactorArea, factorProtoTileCount,
        ConwayLagariasWordFactor.area, protoTileShadowArea, ih]
      all_goals ring

structure LiteralTilingShadowFactorization {m : ℕ}
    (tiling : LiteralTiling m) where
  factors : List ConwayLagariasWordFactor
  boundary_equivalent :
    HasConwayLagariasWordFactorization
      (classZeroBoundaryLabels 1 (m + 3)) factors
  tile_count_exact :
    ∀ tile : ProtoTile,
      factorProtoTileCount factors tile = literalProtoTileCount tiling tile

theorem rightStoneCount_of_shadowFactorization {m : ℕ}
    (tiling : LiteralTiling m)
    (factorization : LiteralTilingShadowFactorization tiling) :
    rightStoneCount tiling = m * (m + 3) / 2 := by
  have hboundary := boundary_identity_of_conwayLagarias_factorization
    factorization.boundary_equivalent
  have harea := congrArg ShadowSummary.areaNumerator hboundary.2
  rw [peripheralBoundary_identityFrame_area] at harea
  simp only at harea
  have hfactor := conwayLagariasFactorArea_eq_stones factorization.factors
  rw [factorization.tile_count_exact .stone,
    literalProtoTileCount_stone] at hfactor
  have hinteger :
      (m : ℤ) * ((m : ℤ) + 3) = 2 * (rightStoneCount tiling : ℤ) := by
    rw [hfactor] at harea
    nlinarith
  have hnatural : m * (m + 3) = 2 * rightStoneCount tiling := by
    exact_mod_cast hinteger
  omega

end BenzelProblem6Kernel
