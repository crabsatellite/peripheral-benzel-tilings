import BenzelProblem6Kernel.LiteralPlacementBoundary
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Sym.Sym2

/-!
# Internal-edge cancellation for labeled honeycomb boundaries
-/

namespace BenzelProblem6Kernel

open scoped symmDiff

abbrev LabeledHexEdgeKey := Sym2 HexVertex × ShadowLabel

def LabeledHexEdge.key (edge : LabeledHexEdge) : LabeledHexEdgeKey :=
  (s(edge.source, edge.target), edge.label)

def labeledBoundaryKeys (edges : List LabeledHexEdge) :
    Finset LabeledHexEdgeKey :=
  edges.toFinset.image LabeledHexEdge.key

def cellBoundaryKeys (cell : Cell) : Finset LabeledHexEdgeKey :=
  labeledBoundaryKeys (labeledCellBoundary cell)

def xorCellBoundaryList : List Cell → Finset LabeledHexEdgeKey
  | [] => ∅
  | cell :: rest => cellBoundaryKeys cell ∆ xorCellBoundaryList rest

def prototypeCellBoundaryXor (tile : ProtoTile) (base : Cell) :
    Finset LabeledHexEdgeKey :=
  xorCellBoundaryList
    ((protoCells tile).map (translateLocalCell base))

def prototypeOuterBoundaryKeys (tile : ProtoTile) (base : Cell) :
    Finset LabeledHexEdgeKey :=
  labeledBoundaryKeys (literalPrototypeBoundary tile base)

def literalPlacementBoundaryKeys {m : ℕ}
    (placement : LiteralPlacement m) : Finset LabeledHexEdgeKey :=
  labeledBoundaryKeys (literalPlacementBoundary placement)

end BenzelProblem6Kernel
