import BenzelProblem6Kernel.GeometricTileBoundarySplice
import Mathlib.Data.List.Count

/-!
# Complete literal-edge peeling traces

Unlike the word-level trace, this certificate records the actual placement
removed at every step and an exact permutation of the original tiling finset.
Consequently no factor or tile multiplicity can be synthesized independently
of the geometric exact cover.
-/

namespace BenzelProblem6Kernel

inductive GeometricBoundaryPeeling (m : ℕ) :
    List LabeledHexEdge → Type
  | done (boundary : List LabeledHexEdge)
      (boundary_empty :
        InvolutiveWordEquivalent (labeledEdgeWord boundary) []) :
      GeometricBoundaryPeeling m boundary
  | peel (boundary : List LabeledHexEdge)
      (splice : GeometricTileBoundarySplice m)
      (boundary_exact : splice.boundary = boundary)
      (nextBoundary : List LabeledHexEdge)
      (remaining_equivalent :
        InvolutiveWordEquivalent
          (labeledEdgeWord splice.remainingBoundary)
          (labeledEdgeWord nextBoundary))
      (rest : GeometricBoundaryPeeling m nextBoundary) :
      GeometricBoundaryPeeling m boundary

def GeometricBoundaryPeeling.factors {m : ℕ} :
    {boundary : List LabeledHexEdge} →
      GeometricBoundaryPeeling m boundary →
        List ConwayLagariasWordFactor
  | _, .done _ _ => []
  | _, .peel _ splice _ _ _ rest =>
      splice.toWordSplice.factor :: rest.factors

def GeometricBoundaryPeeling.placements {m : ℕ} :
    {boundary : List LabeledHexEdge} →
      GeometricBoundaryPeeling m boundary → List (LiteralPlacement m)
  | _, .done _ _ => []
  | _, .peel _ splice _ _ _ rest => splice.placement :: rest.placements

theorem GeometricBoundaryPeeling.factorProtoTileCount_eq_placementCount
    {m : ℕ} {boundary : List LabeledHexEdge}
    (peeling : GeometricBoundaryPeeling m boundary)
    (tile : ProtoTile) :
    factorProtoTileCount peeling.factors tile =
      (peeling.placements.map LiteralPlacement.tile).count tile := by
  induction peeling with
  | done => simp [GeometricBoundaryPeeling.factors,
      GeometricBoundaryPeeling.placements, factorProtoTileCount]
  | peel boundary splice boundary_exact nextBoundary
      remaining_equivalent rest ih =>
      simp only [GeometricBoundaryPeeling.factors,
        GeometricBoundaryPeeling.placements, List.map_cons,
        List.count_cons, factorProtoTileCount,
        ConwayLagariasTileSplice.factor,
        GeometricTileBoundarySplice.toWordSplice]
      rw [ih]
      by_cases htile : splice.placement.tile = tile <;>
        simp [htile, Nat.add_comm]

theorem GeometricBoundaryPeeling.hasFactorization
    {m : ℕ} {boundary : List LabeledHexEdge}
    (peeling : GeometricBoundaryPeeling m boundary) :
    HasConwayLagariasWordFactorization
      (labeledEdgeWord boundary) peeling.factors := by
  induction peeling with
  | done boundary boundary_empty =>
      simpa [HasConwayLagariasWordFactorization,
        GeometricBoundaryPeeling.factors,
        conwayLagariasFactorWord] using boundary_empty
  | peel boundary splice boundary_exact nextBoundary
      remaining_equivalent rest ih =>
      have hstep := splice.word_boundary_equivalent
      rw [boundary_exact] at hstep
      have hnormalize : InvolutiveWordEquivalent
          (splice.toWordSplice.factor.word ++
            labeledEdgeWord splice.remainingBoundary)
          (splice.toWordSplice.factor.word ++
            labeledEdgeWord nextBoundary) :=
        involutiveWordEquivalent_append_left
          splice.toWordSplice.factor.word remaining_equivalent
      have hrest : InvolutiveWordEquivalent
          (splice.toWordSplice.factor.word ++
            labeledEdgeWord nextBoundary)
          (splice.toWordSplice.factor.word ++
            conwayLagariasFactorWord rest.factors) :=
        involutiveWordEquivalent_append_left
          splice.toWordSplice.factor.word ih
      exact Relation.EqvGen.trans _ _ _ hstep
        (Relation.EqvGen.trans _ _ _ hnormalize (by
        simpa [HasConwayLagariasWordFactorization,
          GeometricBoundaryPeeling.factors,
          conwayLagariasFactorWord] using hrest))

theorem literalProtoTileCount_eq_toList_map_count {m : ℕ}
    (tiling : LiteralTiling m) (tile : ProtoTile) :
    literalProtoTileCount tiling tile =
      (tiling.1.toList.map LiteralPlacement.tile).count tile := by
  rw [List.count_eq_countP, List.countP_eq_length_filter,
    List.filter_map, List.length_map]
  let filtered := tiling.1.toList.filter
    (fun placement => placement.tile == tile)
  have hnodup : filtered.Nodup :=
    (Finset.nodup_toList tiling.1).filter _
  change literalProtoTileCount tiling tile = filtered.length
  rw [← List.toFinset_card_of_nodup hnodup]
  unfold literalProtoTileCount
  apply congrArg Finset.card
  dsimp [filtered]
  rw [List.toFinset_filter, Finset.toList_toFinset]
  ext placement
  simp only [Finset.mem_filter, beq_iff_eq]

structure LiteralTilingGeometricPeeling {m : ℕ}
    (tiling : LiteralTiling m) where
  peeling : GeometricBoundaryPeeling m
    (literalReducedPeripheralBoundary m)
  placements_exact : List.Perm peeling.placements tiling.1.toList

def LiteralTilingGeometricPeeling.toReducedFactorization
    {m : ℕ} {tiling : LiteralTiling m}
    (certificate : LiteralTilingGeometricPeeling tiling) :
    LiteralReducedBoundaryFactorization tiling where
  factors := certificate.peeling.factors
  boundary_equivalent := certificate.peeling.hasFactorization
  tile_count_exact := by
    intro tile
    rw [certificate.peeling.factorProtoTileCount_eq_placementCount,
      (certificate.placements_exact.map LiteralPlacement.tile).count_eq tile,
      ← literalProtoTileCount_eq_toList_map_count]

theorem rightStoneCount_of_geometricPeeling {m : ℕ}
    (tiling : LiteralTiling m)
    (certificate : LiteralTilingGeometricPeeling tiling) :
    rightStoneCount tiling = m * (m + 3) / 2 := by
  exact rightStoneCount_of_reducedBoundaryFactorization tiling
    certificate.toReducedFactorization

end BenzelProblem6Kernel
