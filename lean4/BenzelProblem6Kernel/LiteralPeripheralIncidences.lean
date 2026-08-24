import BenzelProblem6Kernel.BenzelBoundaryParity

/-!
# Explicit interior cell-sides on the peripheral boundary

The list is ordered along the reflected clockwise six-block walk, but every
entry stores the unique interior cell and its counterclockwise side.  The
three augmented spurs are omitted.  Its length is therefore `12m + 42`, the
literal perimeter.
-/

namespace BenzelProblem6Kernel

abbrev CellSide := Cell × HexSide

def peripheralFixed₀ (m : ℕ) : List CellSide :=
  [(((m : ℤ) + 3, 1), .side₅),
    (((m : ℤ) + 3, 1), .side₄),
    (((m : ℤ) + 3, 0), .side₅)]

def peripheralLong₁Entry (m r : ℕ) : List CellSide :=
  (if r = 0 then [] else
    [(((m : ℤ) - r + 4, -(r : ℤ)), .side₃)]) ++
  [(((m : ℤ) - r + 3, -(r : ℤ)), .side₄),
    (((m : ℤ) - r + 3, -(r : ℤ) - 1), .side₅),
    (((m : ℤ) - r + 3, -(r : ℤ) - 1), .side₄)]

def peripheralLong₁ (m : ℕ) : List CellSide :=
  (List.range (m + 3)).flatMap (peripheralLong₁Entry m)

def peripheralFixed₂ (m : ℕ) : List CellSide :=
  [((1, -((m : ℤ)) - 3), .side₃),
    ((1, -((m : ℤ)) - 3), .side₂),
    ((0, -((m : ℤ)) - 2), .side₃)]

def peripheralLong₃Entry (m r : ℕ) : List CellSide :=
  (if r = 0 then [] else
    [((-(r : ℤ), -((m : ℤ)) + 2 * r - 3), .side₁)]) ++
  [((-(r : ℤ), -((m : ℤ)) + 2 * r - 2), .side₂),
    ((-(r : ℤ) - 1, -((m : ℤ)) + 2 * r - 1), .side₃),
    ((-(r : ℤ) - 1, -((m : ℤ)) + 2 * r - 1), .side₂)]

def peripheralLong₃ (m : ℕ) : List CellSide :=
  (List.range (m + 3)).flatMap (peripheralLong₃Entry m)

def peripheralFixed₄ (m : ℕ) : List CellSide :=
  [((-((m : ℤ)) - 3, (m : ℤ) + 3), .side₁),
    ((-((m : ℤ)) - 3, (m : ℤ) + 3), .side₀),
    ((-((m : ℤ)) - 2, (m : ℤ) + 3), .side₁)]

def peripheralLong₅Entry (m r : ℕ) : List CellSide :=
  (if r = 0 then [] else
    [((-((m : ℤ)) + 2 * r - 3, (m : ℤ) - r + 4), .side₅)]) ++
  [((-((m : ℤ)) + 2 * r - 2, (m : ℤ) - r + 3), .side₀),
    ((-((m : ℤ)) + 2 * r - 1, (m : ℤ) - r + 3), .side₁),
    ((-((m : ℤ)) + 2 * r - 1, (m : ℤ) - r + 3), .side₀)]

def peripheralLong₅ (m : ℕ) : List CellSide :=
  (List.range (m + 3)).flatMap (peripheralLong₅Entry m)

def literalPeripheralIncidences (m : ℕ) : List CellSide :=
  peripheralFixed₀ m ++ peripheralLong₁ m ++
    peripheralFixed₂ m ++ peripheralLong₃ m ++
    peripheralFixed₄ m ++ peripheralLong₅ m

def IsInsidePeripheralEdge (m : ℕ) (cell : Cell)
    (side : HexSide) : Prop :=
  inPeripheralBenzel (m + 5) cell ∧
    ¬inPeripheralBenzel (m + 5) (neighboringCell cell side)

end BenzelProblem6Kernel
