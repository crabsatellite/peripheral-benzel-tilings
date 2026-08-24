import BenzelProblem6Kernel.LiteralHexBoundary

/-!
# Exact labeled outer boundaries of literal prototile placements
-/

namespace BenzelProblem6Kernel

def prototypeBoundaryStart (tile : ProtoTile) (base : Cell) : HexVertex :=
  match tile with
  | .stone | .boneA | .boneB =>
      let center := hexCellCenter base
      (center.1 - 1, center.2 - 1)
  | .boneC =>
      let center := hexCellCenter base
      (center.1 - 3, center.2 - 5)

def prototypeBoundarySteps : ProtoTile → List LabeledHexStep
  | .stone =>
      [(shadowA, .a), (shadowB.neg, .b),
        (shadowA, .a), (shadowC.neg, .c),
        (shadowB, .b), (shadowC.neg, .c),
        (shadowB, .b), (shadowA.neg, .a),
        (shadowC, .c), (shadowA.neg, .a),
        (shadowC, .c), (shadowB.neg, .b)]
  | .boneA =>
      [(shadowA, .a), (shadowB.neg, .b),
        (shadowA, .a), (shadowB.neg, .b),
        (shadowA, .a), (shadowC.neg, .c),
        (shadowB, .b), (shadowA.neg, .a),
        (shadowB, .b), (shadowA.neg, .a),
        (shadowB, .b), (shadowA.neg, .a),
        (shadowC, .c), (shadowB.neg, .b)]
  | .boneB =>
      [(shadowA, .a), (shadowC.neg, .c),
        (shadowA, .a), (shadowC.neg, .c),
        (shadowA, .a), (shadowC.neg, .c),
        (shadowB, .b), (shadowA.neg, .a),
        (shadowC, .c), (shadowA.neg, .a),
        (shadowC, .c), (shadowA.neg, .a),
        (shadowC, .c), (shadowB.neg, .b)]
  | .boneC =>
      [(shadowA, .a), (shadowC.neg, .c),
        (shadowB, .b), (shadowC.neg, .c),
        (shadowB, .b), (shadowC.neg, .c),
        (shadowB, .b), (shadowA.neg, .a),
        (shadowC, .c), (shadowB.neg, .b),
        (shadowC, .c), (shadowB.neg, .b),
        (shadowC, .c), (shadowB.neg, .b)]

def literalPrototypeBoundary (tile : ProtoTile) (base : Cell) :
    List LabeledHexEdge :=
  walkLabeledHexEdges (prototypeBoundaryStart tile base)
    (prototypeBoundarySteps tile)

def literalPlacementBoundary {m : ℕ} (placement : LiteralPlacement m) :
    List LabeledHexEdge :=
  literalPrototypeBoundary placement.tile placement.base

def labeledEdgeWord (edges : List LabeledHexEdge) : List ShadowLabel :=
  edges.map LabeledHexEdge.label

theorem labeledEdgeWord_walk (source : HexVertex)
    (steps : List LabeledHexStep) :
    labeledEdgeWord (walkLabeledHexEdges source steps) = steps.map Prod.snd := by
  induction steps generalizing source with
  | nil => rfl
  | cons step rest ih =>
      simp only [walkLabeledHexEdges, labeledEdgeWord, List.map_cons,
        List.cons.injEq]
      exact ⟨rfl, ih _⟩

theorem prototypeBoundarySteps_labels (tile : ProtoTile) :
    (prototypeBoundarySteps tile).map Prod.snd =
      protoTileBoundaryLabels tile := by
  cases tile <;> decide

theorem literalPrototypeBoundary_word (tile : ProtoTile) (base : Cell) :
    labeledEdgeWord (literalPrototypeBoundary tile base) =
      protoTileBoundaryLabels tile := by
  rw [literalPrototypeBoundary, labeledEdgeWord_walk,
    prototypeBoundarySteps_labels]

theorem literalPlacementBoundary_word {m : ℕ}
    (placement : LiteralPlacement m) :
    labeledEdgeWord (literalPlacementBoundary placement) =
      protoTileBoundaryLabels placement.tile :=
  literalPrototypeBoundary_word placement.tile placement.base

theorem literalPrototypeBoundary_closed (tile : ProtoTile) (base : Cell) :
    (literalPrototypeBoundary tile base).getLast?.map LabeledHexEdge.target =
      (literalPrototypeBoundary tile base).head?.map LabeledHexEdge.source := by
  cases tile <;>
    simp [literalPrototypeBoundary, prototypeBoundarySteps,
      prototypeBoundaryStart, walkLabeledHexEdges,
      advanceLabeledHexEdge, addHexStep, ShadowStep.neg,
      shadowA, shadowB, shadowC, hexCellCenter] <;>
    ring
  all_goals simp

end BenzelProblem6Kernel
