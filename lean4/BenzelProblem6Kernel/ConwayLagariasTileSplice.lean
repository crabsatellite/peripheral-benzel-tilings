import BenzelProblem6Kernel.InvolutiveWordSplicing

/-!
# A geometric boundary splice as one Conway--Lagarias factor

The shared edge may occur at different cyclic positions in the region and tile
words.  Conjugating by `regionPrefix ++ reverse tilePrefix` aligns those
basepoints.  Its evenness is exactly the physical `L₀/L₁` parity condition.
-/

namespace BenzelProblem6Kernel

theorem shadowConjugate_cyclic_alignment
    (before tilePrefix tileSuffix : List ShadowLabel) :
    InvolutiveWordEquivalent
      (shadowConjugate (before ++ tilePrefix.reverse)
        (tilePrefix ++ tileSuffix))
      (shadowConjugate before (tileSuffix ++ tilePrefix)) := by
  let afterPrefixCancellation :=
    before ++ tileSuffix ++ tilePrefix ++ before.reverse
  have hprefix : InvolutiveWordEquivalent
      (shadowConjugate (before ++ tilePrefix.reverse)
        (tilePrefix ++ tileSuffix)) afterPrefixCancellation := by
    have hcancel := reverse_append_word_equivalent_empty tilePrefix
    simpa [shadowConjugate, afterPrefixCancellation,
      List.reverse_append, List.append_assoc] using
        involutiveWordEquivalent_append_context before
          (tileSuffix ++ tilePrefix ++ before.reverse) hcancel
  have hshape :
      afterPrefixCancellation =
        shadowConjugate before (tileSuffix ++ tilePrefix) := by
    simp [afterPrefixCancellation, shadowConjugate,
      List.append_assoc]
  rw [hshape] at hprefix
  exact hprefix

structure ConwayLagariasTileSplice where
  boundary : List ShadowLabel
  tile : ProtoTile
  boundaryPrefix : List ShadowLabel
  boundarySuffix : List ShadowLabel
  tilePrefix : List ShadowLabel
  tileSuffix : List ShadowLabel
  sharedLabel : ShadowLabel
  boundary_eq :
    boundary = boundaryPrefix ++ sharedLabel :: boundarySuffix
  tile_eq :
    protoTileBoundaryLabels tile =
      tilePrefix ++ sharedLabel :: tileSuffix
  factor_path_even :
    EvenShadowLabelWord (boundaryPrefix ++ tilePrefix.reverse)

def ConwayLagariasTileSplice.factor
    (splice : ConwayLagariasTileSplice) :
    ConwayLagariasWordFactor where
  tile := splice.tile
  path := splice.boundaryPrefix ++ splice.tilePrefix.reverse
  path_even := splice.factor_path_even

def ConwayLagariasTileSplice.rotatedTileRest
    (splice : ConwayLagariasTileSplice) : List ShadowLabel :=
  splice.tileSuffix ++ splice.tilePrefix

def ConwayLagariasTileSplice.remainingBoundary
    (splice : ConwayLagariasTileSplice) : List ShadowLabel :=
  spliceTileRestIntoBoundary splice.boundaryPrefix
    splice.rotatedTileRest splice.boundarySuffix

theorem ConwayLagariasTileSplice.factor_word_equivalent_rotated
    (splice : ConwayLagariasTileSplice) :
    InvolutiveWordEquivalent splice.factor.word
      (shadowConjugate splice.boundaryPrefix
        (splice.sharedLabel :: splice.rotatedTileRest)) := by
  rw [ConwayLagariasWordFactor.word,
    ConwayLagariasTileSplice.factor,
    splice.tile_eq]
  simpa [ConwayLagariasTileSplice.rotatedTileRest,
    List.append_assoc] using shadowConjugate_cyclic_alignment
      splice.boundaryPrefix splice.tilePrefix
        (splice.sharedLabel :: splice.tileSuffix)

theorem ConwayLagariasTileSplice.boundary_equivalent_factor_remaining
    (splice : ConwayLagariasTileSplice) :
    InvolutiveWordEquivalent splice.boundary
      (splice.factor.word ++ splice.remainingBoundary) := by
  rw [splice.boundary_eq]
  have hfactor := splice.factor_word_equivalent_rotated
  have hfactorContext := involutiveWordEquivalent_append_right hfactor
    splice.remainingBoundary
  have hsplice := boundary_equivalent_factorWord_append_splice
    splice.boundaryPrefix splice.sharedLabel splice.rotatedTileRest
      splice.boundarySuffix
  exact Relation.EqvGen.trans _ _ _ hsplice
    (Relation.EqvGen.symm _ _ (by
      simpa [ConwayLagariasTileSplice.remainingBoundary] using hfactorContext))

theorem factorProtoTileCount_cons_splice
    (splice : ConwayLagariasTileSplice)
    (rest : List ConwayLagariasWordFactor) (tile : ProtoTile) :
    factorProtoTileCount (splice.factor :: rest) tile =
      (if splice.tile = tile then 1 else 0) +
        factorProtoTileCount rest tile := by
  rfl

end BenzelProblem6Kernel
