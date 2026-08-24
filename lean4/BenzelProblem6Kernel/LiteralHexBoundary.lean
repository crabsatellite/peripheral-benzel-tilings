import BenzelProblem6Kernel.LiteralTilingShadowFactorization

/-!
# Literal honeycomb vertices and labeled cell boundaries
-/

namespace BenzelProblem6Kernel

abbrev HexVertex := ℤ × ℤ

def hexCellCenter (cell : Cell) : HexVertex :=
  (-1 + cell.1 + 2 * cell.2, -cell.1 + cell.2)

def addHexStep (vertex : HexVertex) (step : ShadowStep) : HexVertex :=
  (vertex.1 + step.x, vertex.2 + step.y)

def hexCellStartVertex (cell : Cell) : HexVertex :=
  addHexStep (hexCellCenter cell) shadowA

structure LabeledHexEdge where
  source : HexVertex
  target : HexVertex
  label : ShadowLabel
  deriving DecidableEq

@[ext] theorem labeledHexEdge_ext (left right : LabeledHexEdge)
    (hsource : left.source = right.source)
    (htarget : left.target = right.target)
    (hlabel : left.label = right.label) : left = right := by
  cases left
  cases right
  simp_all

def advanceLabeledHexEdge (source : HexVertex)
    (step : ShadowStep) (label : ShadowLabel) : LabeledHexEdge :=
  ⟨source, addHexStep source step, label⟩

abbrev LabeledHexStep := ShadowStep × ShadowLabel

def walkLabeledHexEdges : HexVertex → List LabeledHexStep →
    List LabeledHexEdge
  | _source, [] => []
  | source, step :: rest =>
      let edge := advanceLabeledHexEdge source step.1 step.2
      edge :: walkLabeledHexEdges edge.target rest

def cellBoundarySteps : List LabeledHexStep :=
  [(shadowB, .b), (shadowA.neg, .a), (shadowC, .c),
    (shadowB.neg, .b), (shadowA, .a), (shadowC.neg, .c)]

def labeledCellBoundary (cell : Cell) : List LabeledHexEdge :=
  walkLabeledHexEdges (hexCellStartVertex cell) cellBoundarySteps

def labeledCellBoundaryWord (cell : Cell) : List ShadowLabel :=
  (labeledCellBoundary cell).map LabeledHexEdge.label

theorem labeledCellBoundaryWord_eq (cell : Cell) :
    labeledCellBoundaryWord cell = [.b, .a, .c, .b, .a, .c] := by
  rfl

theorem labeledCellBoundary_closed (cell : Cell) :
    (labeledCellBoundary cell).getLast?.map LabeledHexEdge.target =
      (labeledCellBoundary cell).head?.map LabeledHexEdge.source := by
  simp [labeledCellBoundary, advanceLabeledHexEdge, addHexStep,
    walkLabeledHexEdges, cellBoundarySteps, hexCellStartVertex,
    ShadowStep.neg, shadowA, shadowB, shadowC]

end BenzelProblem6Kernel
