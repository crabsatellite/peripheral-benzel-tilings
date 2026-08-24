import BenzelProblem6Kernel.LiteralTilingOuterBoundary

/-! # The one-tile base case of the Conway--Lagarias induction -/

namespace BenzelProblem6Kernel

def literalPlacementFactor {m : ℕ}
    (placement : LiteralPlacement m) : ConwayLagariasWordFactor where
  tile := placement.tile
  path := []
  path_even := ⟨0, rfl⟩

theorem literalPlacementFactor_word {m : ℕ}
    (placement : LiteralPlacement m) :
    (literalPlacementFactor placement).word =
      protoTileBoundaryLabels placement.tile := by
  simp [ConwayLagariasWordFactor.word, literalPlacementFactor,
    shadowConjugate]

theorem literalPlacementBoundary_has_singleFactor {m : ℕ}
    (placement : LiteralPlacement m) :
    HasConwayLagariasWordFactorization
      (labeledEdgeWord (literalPlacementBoundary placement))
      [literalPlacementFactor placement] := by
  rw [literalPlacementBoundary_word,
    HasConwayLagariasWordFactorization]
  simp only [conwayLagariasFactorWord, literalPlacementFactor_word,
    List.append_nil]
  simpa using Relation.EqvGen.refl
    (protoTileBoundaryLabels placement.tile)

theorem factorProtoTileCount_singlePlacement {m : ℕ}
    (placement : LiteralPlacement m) (tile : ProtoTile) :
    factorProtoTileCount [literalPlacementFactor placement] tile =
      if placement.tile = tile then 1 else 0 := by
  simp [factorProtoTileCount, literalPlacementFactor]

end BenzelProblem6Kernel
