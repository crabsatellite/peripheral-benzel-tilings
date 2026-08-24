import BenzelProblem6Kernel.ConwayLagariasFactorComposition

/-!
# Exact consumer of a literal reduced-boundary factorization

This file consumes a planar face factorization together with the reflected
outer-word identities, spur reductions, local tile areas, exact tile
multiplicities, and natural-number arithmetic.
-/

namespace BenzelProblem6Kernel

structure LiteralReducedBoundaryFactorization {m : ℕ}
    (tiling : LiteralTiling m) where
  factors : List ConwayLagariasWordFactor
  boundary_equivalent :
    HasConwayLagariasWordFactorization
      (labeledEdgeWord (literalReducedPeripheralBoundary m)) factors
  tile_count_exact :
    ∀ tile : ProtoTile,
      factorProtoTileCount factors tile = literalProtoTileCount tiling tile

theorem literalBoundary_has_factorization_of_reduced {m : ℕ}
    {tiling : LiteralTiling m}
    (factorization : LiteralReducedBoundaryFactorization tiling) :
    HasConwayLagariasWordFactorization
      (literalPeripheralBoundaryLabels m) factorization.factors := by
  exact Relation.EqvGen.trans _ _ _
    (literalPeripheralBoundary_equivalent_reduced m)
    factorization.boundary_equivalent

theorem rightStoneCount_of_reducedBoundaryFactorization {m : ℕ}
    (tiling : LiteralTiling m)
    (factorization : LiteralReducedBoundaryFactorization tiling) :
    rightStoneCount tiling = m * (m + 3) / 2 := by
  have hfactorIdentity := boundary_identity_of_conwayLagarias_factorization
    (literalBoundary_has_factorization_of_reduced factorization)
  have houterIdentity := literalPeripheralBoundary_identity m
  have hsummary :
      (⟨0, 0, conwayLagariasFactorArea factorization.factors⟩ :
          ShadowSummary) =
        ⟨0, 0, 9 * (m : ℤ) * (m + 3)⟩ := by
    exact hfactorIdentity.2.symm.trans houterIdentity.2
  have harea := congrArg ShadowSummary.areaNumerator hsummary
  have hfactorArea := conwayLagariasFactorArea_eq_stones
    factorization.factors
  rw [factorization.tile_count_exact .stone,
    literalProtoTileCount_stone] at hfactorArea
  have hinteger :
      (m : ℤ) * ((m : ℤ) + 3) =
        2 * (rightStoneCount tiling : ℤ) := by
    rw [hfactorArea] at harea
    change 18 * (rightStoneCount tiling : ℤ) =
      9 * (m : ℤ) * ((m : ℤ) + 3) at harea
    nlinarith
  have hnatural :
      m * (m + 3) = 2 * rightStoneCount tiling := by
    exact_mod_cast hinteger
  omega

end BenzelProblem6Kernel
