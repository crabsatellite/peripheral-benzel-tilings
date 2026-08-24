import BenzelProblem6Kernel.ConwayLagariasTileSplice

/-!
# A complete boundary-peeling certificate

A peeling is the exact finite witness needed from planar geometry.  Each step
removes one tile along a shared oriented edge using the previous splice
producer; the terminal walk must freely cancel to the empty word.  The derived
factor list and tile list are data, not propositions hidden behind an adapter.
-/

namespace BenzelProblem6Kernel

inductive ConwayLagariasBoundaryPeeling : List ShadowLabel → Type
  | done (boundary : List ShadowLabel)
      (boundary_empty : InvolutiveWordEquivalent boundary []) :
      ConwayLagariasBoundaryPeeling boundary
  | peel (boundary : List ShadowLabel)
      (splice : ConwayLagariasTileSplice)
      (boundary_exact : splice.boundary = boundary)
      (rest : ConwayLagariasBoundaryPeeling splice.remainingBoundary) :
      ConwayLagariasBoundaryPeeling boundary

def ConwayLagariasBoundaryPeeling.factors :
    {boundary : List ShadowLabel} →
      ConwayLagariasBoundaryPeeling boundary →
        List ConwayLagariasWordFactor
  | _, .done _ _ => []
  | _, .peel _ splice _ rest => splice.factor :: rest.factors

def ConwayLagariasBoundaryPeeling.tiles :
    {boundary : List ShadowLabel} →
      ConwayLagariasBoundaryPeeling boundary → List ProtoTile
  | _, .done _ _ => []
  | _, .peel _ splice _ rest => splice.tile :: rest.tiles

theorem ConwayLagariasBoundaryPeeling.factorProtoTileCount_eq_count
    {boundary : List ShadowLabel}
    (peeling : ConwayLagariasBoundaryPeeling boundary)
    (tile : ProtoTile) :
    factorProtoTileCount peeling.factors tile =
      peeling.tiles.count tile := by
  induction peeling with
  | done => simp [ConwayLagariasBoundaryPeeling.factors,
      ConwayLagariasBoundaryPeeling.tiles, factorProtoTileCount]
  | peel boundary splice boundary_exact rest ih =>
      simp only [ConwayLagariasBoundaryPeeling.factors,
        ConwayLagariasBoundaryPeeling.tiles, List.count_cons,
        factorProtoTileCount, ConwayLagariasTileSplice.factor]
      rw [ih]
      by_cases htile : splice.tile = tile <;>
        simp [htile, Nat.add_comm]

theorem ConwayLagariasBoundaryPeeling.hasFactorization
    {boundary : List ShadowLabel}
    (peeling : ConwayLagariasBoundaryPeeling boundary) :
    HasConwayLagariasWordFactorization boundary peeling.factors := by
  induction peeling with
  | done boundary boundary_empty =>
      simpa [HasConwayLagariasWordFactorization,
        ConwayLagariasBoundaryPeeling.factors,
        conwayLagariasFactorWord] using boundary_empty
  | peel boundary splice boundary_exact rest ih =>
      have hstep := splice.boundary_equivalent_factor_remaining
      rw [boundary_exact] at hstep
      have hrest : InvolutiveWordEquivalent
          (splice.factor.word ++ splice.remainingBoundary)
          (splice.factor.word ++ conwayLagariasFactorWord rest.factors) :=
        involutiveWordEquivalent_append_left splice.factor.word ih
      exact Relation.EqvGen.trans _ _ _ hstep (by
        simpa [HasConwayLagariasWordFactorization,
          ConwayLagariasBoundaryPeeling.factors,
          conwayLagariasFactorWord] using hrest)

structure LiteralTilingBoundaryPeeling {m : ℕ}
    (tiling : LiteralTiling m) where
  peeling : ConwayLagariasBoundaryPeeling
    (labeledEdgeWord (literalReducedPeripheralBoundary m))
  tile_count_exact :
    ∀ tile : ProtoTile,
      peeling.tiles.count tile = literalProtoTileCount tiling tile

def LiteralTilingBoundaryPeeling.toReducedFactorization
    {m : ℕ} {tiling : LiteralTiling m}
    (certificate : LiteralTilingBoundaryPeeling tiling) :
    LiteralReducedBoundaryFactorization tiling where
  factors := certificate.peeling.factors
  boundary_equivalent := certificate.peeling.hasFactorization
  tile_count_exact := by
    intro tile
    rw [certificate.peeling.factorProtoTileCount_eq_count,
      certificate.tile_count_exact]

theorem rightStoneCount_of_boundaryPeeling {m : ℕ}
    (tiling : LiteralTiling m)
    (certificate : LiteralTilingBoundaryPeeling tiling) :
    rightStoneCount tiling = m * (m + 3) / 2 := by
  exact rightStoneCount_of_reducedBoundaryFactorization tiling
    certificate.toReducedFactorization

end BenzelProblem6Kernel
