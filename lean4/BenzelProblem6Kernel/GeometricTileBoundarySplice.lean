import BenzelProblem6Kernel.ConwayLagariasBoundaryPeeling

/-!
# From an oriented geometric tile splice to a word splice

The witness below uses literal honeycomb edges.  The same oriented edge must
occur in both the current region walk and the literal placement boundary.
Mapping labels then produces exactly the noncommutative splice consumed by the
Conway--Lagarias peeling layer.
-/

namespace BenzelProblem6Kernel

theorem labeledEdgeWord_append (left right : List LabeledHexEdge) :
    labeledEdgeWord (left ++ right) =
      labeledEdgeWord left ++ labeledEdgeWord right := by
  simp [labeledEdgeWord]

theorem labeledEdgeWord_singleton (edge : LabeledHexEdge) :
    labeledEdgeWord [edge] = [edge.label] := rfl

theorem labeledEdgeWord_reverse (edges : List LabeledHexEdge) :
    labeledEdgeWord edges.reverse = (labeledEdgeWord edges).reverse := by
  simp [labeledEdgeWord]

theorem labeledEdgeWord_reverseReoriented
    (edges : List LabeledHexEdge) :
    labeledEdgeWord (edges.reverse.map reverseLabeledHexEdge) =
      (labeledEdgeWord edges).reverse :=
  labeledEdgeWord_reverseEdges edges

structure GeometricTileBoundarySplice (m : ℕ) where
  boundary : List LabeledHexEdge
  placement : LiteralPlacement m
  boundaryPrefix : List LabeledHexEdge
  boundarySuffix : List LabeledHexEdge
  tilePrefix : List LabeledHexEdge
  tileSuffix : List LabeledHexEdge
  sharedEdge : LabeledHexEdge
  boundary_eq :
    boundary = boundaryPrefix ++ sharedEdge :: boundarySuffix
  tile_eq :
    literalPlacementBoundary placement =
      tilePrefix ++ sharedEdge :: tileSuffix
  factor_path_even :
    EvenShadowLabelWord
      (labeledEdgeWord boundaryPrefix ++
        (labeledEdgeWord tilePrefix).reverse)

def GeometricTileBoundarySplice.rotatedTileRest
    {m : ℕ} (splice : GeometricTileBoundarySplice m) :
    List LabeledHexEdge :=
  splice.tileSuffix ++ splice.tilePrefix

def GeometricTileBoundarySplice.remainingBoundary
    {m : ℕ} (splice : GeometricTileBoundarySplice m) :
    List LabeledHexEdge :=
  splice.boundaryPrefix ++
    splice.rotatedTileRest.reverse.map reverseLabeledHexEdge ++
    splice.boundarySuffix

def GeometricTileBoundarySplice.toWordSplice
    {m : ℕ} (splice : GeometricTileBoundarySplice m) :
    ConwayLagariasTileSplice where
  boundary := labeledEdgeWord splice.boundary
  tile := splice.placement.tile
  boundaryPrefix := labeledEdgeWord splice.boundaryPrefix
  boundarySuffix := labeledEdgeWord splice.boundarySuffix
  tilePrefix := labeledEdgeWord splice.tilePrefix
  tileSuffix := labeledEdgeWord splice.tileSuffix
  sharedLabel := splice.sharedEdge.label
  boundary_eq := by
    rw [splice.boundary_eq, labeledEdgeWord_append]
    rfl
  tile_eq := by
    rw [← literalPlacementBoundary_word splice.placement,
      splice.tile_eq, labeledEdgeWord_append]
    rfl
  factor_path_even := splice.factor_path_even

theorem GeometricTileBoundarySplice.word_remainingBoundary
    {m : ℕ} (splice : GeometricTileBoundarySplice m) :
    labeledEdgeWord splice.remainingBoundary =
      splice.toWordSplice.remainingBoundary := by
  simp only [GeometricTileBoundarySplice.remainingBoundary,
    ConwayLagariasTileSplice.remainingBoundary,
    spliceTileRestIntoBoundary,
    GeometricTileBoundarySplice.toWordSplice,
    GeometricTileBoundarySplice.rotatedTileRest,
    ConwayLagariasTileSplice.rotatedTileRest,
    labeledEdgeWord_append, labeledEdgeWord_reverseReoriented,
    List.map_append, List.reverse_append]

theorem GeometricTileBoundarySplice.word_boundary_equivalent
    {m : ℕ} (splice : GeometricTileBoundarySplice m) :
    InvolutiveWordEquivalent (labeledEdgeWord splice.boundary)
      (splice.toWordSplice.factor.word ++
        labeledEdgeWord splice.remainingBoundary) := by
  rw [splice.word_remainingBoundary]
  exact splice.toWordSplice.boundary_equivalent_factor_remaining

end BenzelProblem6Kernel
