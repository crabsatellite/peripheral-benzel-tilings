import BenzelProblem6Kernel.LiteralPeripheralBoundaryWalk

/-!
# Unique incidence of labeled honeycomb edges

Every labeled unoriented honeycomb edge belongs to exactly two cells.  The
second cell and its opposite side are explicit below.  This is the local
geometric producer needed to turn symmetric-difference membership into a
literal inside/outside boundary test.
-/

namespace BenzelProblem6Kernel

inductive HexSide
  | side₀
  | side₁
  | side₂
  | side₃
  | side₄
  | side₅
  deriving DecidableEq

def oppositeHexSide : HexSide → HexSide
  | .side₀ => .side₃
  | .side₁ => .side₄
  | .side₂ => .side₅
  | .side₃ => .side₀
  | .side₄ => .side₁
  | .side₅ => .side₂

def neighboringCell : Cell → HexSide → Cell
  | (i, j), .side₀ => (i, j + 1)
  | (i, j), .side₁ => (i - 1, j + 1)
  | (i, j), .side₂ => (i - 1, j)
  | (i, j), .side₃ => (i, j - 1)
  | (i, j), .side₄ => (i + 1, j - 1)
  | (i, j), .side₅ => (i + 1, j)

theorem neighboringCell_opposite (cell : Cell) (side : HexSide) :
    neighboringCell (neighboringCell cell side) (oppositeHexSide side) =
      cell := by
  rcases cell with ⟨i, j⟩
  cases side <;> simp [neighboringCell, oppositeHexSide]

theorem neighboringCell_ne (cell : Cell) (side : HexSide) :
    neighboringCell cell side ≠ cell := by
  rcases cell with ⟨i, j⟩
  cases side <;> simp [neighboringCell]

def cellBoundaryEdgeAt (cell : Cell) : HexSide → LabeledHexEdge
  | .side₀ =>
      advanceLabeledHexEdge (hexCellStartVertex cell) shadowB .b
  | .side₁ =>
      advanceLabeledHexEdge
        (addHexStep (hexCellStartVertex cell) shadowB) shadowA.neg .a
  | .side₂ =>
      advanceLabeledHexEdge
        (addHexStep
          (addHexStep (hexCellStartVertex cell) shadowB) shadowA.neg)
        shadowC .c
  | .side₃ =>
      advanceLabeledHexEdge
        (addHexStep
          (addHexStep
            (addHexStep (hexCellStartVertex cell) shadowB) shadowA.neg)
          shadowC)
        shadowB.neg .b
  | .side₄ =>
      advanceLabeledHexEdge
        (addHexStep
          (addHexStep
            (addHexStep
              (addHexStep (hexCellStartVertex cell) shadowB) shadowA.neg)
            shadowC)
          shadowB.neg)
        shadowA .a
  | .side₅ =>
      advanceLabeledHexEdge
        (addHexStep
          (addHexStep
            (addHexStep
              (addHexStep
                (addHexStep (hexCellStartVertex cell) shadowB) shadowA.neg)
              shadowC)
            shadowB.neg)
          shadowA)
        shadowC.neg .c

def allCellBoundaryEdges (cell : Cell) : List LabeledHexEdge :=
  [cellBoundaryEdgeAt cell .side₀,
    cellBoundaryEdgeAt cell .side₁,
    cellBoundaryEdgeAt cell .side₂,
    cellBoundaryEdgeAt cell .side₃,
    cellBoundaryEdgeAt cell .side₄,
    cellBoundaryEdgeAt cell .side₅]

theorem labeledCellBoundary_eq_allEdges (cell : Cell) :
    labeledCellBoundary cell = allCellBoundaryEdges cell := by
  rfl

theorem cellBoundaryEdgeAt_neighbor (cell : Cell) (side : HexSide) :
    (cellBoundaryEdgeAt cell side).key =
      (cellBoundaryEdgeAt (neighboringCell cell side)
        (oppositeHexSide side)).key := by
  rcases cell with ⟨i, j⟩
  cases side <;>
    apply Prod.ext <;>
    simp [cellBoundaryEdgeAt, neighboringCell, oppositeHexSide,
      LabeledHexEdge.key, advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, Sym2.eq_iff] <;> omega

end BenzelProblem6Kernel
