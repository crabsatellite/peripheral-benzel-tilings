import BenzelProblem6Kernel.LiteralPeripheralBoundaryKeys

/-!
# The reduced literal peripheral boundary word

The arithmetic incidence list omits the three augmented spurs.  This file
computes its label word exactly, with the same cache boundaries as the six
geometric sides.
-/

namespace BenzelProblem6Kernel

def cellSideBoundaryLabel (datum : CellSide) : ShadowLabel :=
  (cellSideBoundaryEdge datum).label

theorem cellSideBoundaryLabel_eq (cell : Cell) (side : HexSide) :
    cellSideBoundaryLabel (cell, side) =
      match side with
      | .side₀ | .side₃ => .b
      | .side₁ | .side₄ => .a
      | .side₂ | .side₅ => .c := by
  cases side <;> rfl

theorem flatMap_range_const_word (word : List ShadowLabel) (count : ℕ) :
    (List.range count).flatMap (fun _ => word) =
      shadowLabelWordPower word count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.flatMap_append,
        shadowLabelWordPower_succ, ih]
      simp

theorem peripheralLong₁_labels (m : ℕ) :
    (peripheralLong₁ m).map cellSideBoundaryLabel =
      [.a, .c, .a] ++
        shadowLabelWordPower [.b, .a, .c, .a] (m + 2) := by
  rw [peripheralLong₁, List.map_flatMap,
    show m + 3 = (m + 2) + 1 by omega,
    List.range_succ_eq_map, List.flatMap_cons,
    List.flatMap_map]
  simp [peripheralLong₁Entry, cellSideBoundaryLabel_eq]
  rw [flatMap_range_const_word]
  rw [show m + 2 = (m + 1) + 1 by omega,
    shadowLabelWordPower_succ, shadowLabelWordPower_succ]
  simp [List.append_assoc]

theorem peripheralLong₃_labels (m : ℕ) :
    (peripheralLong₃ m).map cellSideBoundaryLabel =
      [.c, .b, .c] ++
        shadowLabelWordPower [.a, .c, .b, .c] (m + 2) := by
  rw [peripheralLong₃, List.map_flatMap,
    show m + 3 = (m + 2) + 1 by omega,
    List.range_succ_eq_map, List.flatMap_cons,
    List.flatMap_map]
  simp [peripheralLong₃Entry, cellSideBoundaryLabel_eq]
  rw [flatMap_range_const_word]
  rw [show m + 2 = (m + 1) + 1 by omega,
    shadowLabelWordPower_succ, shadowLabelWordPower_succ]
  simp [List.append_assoc]

theorem peripheralLong₅_labels (m : ℕ) :
    (peripheralLong₅ m).map cellSideBoundaryLabel =
      [.b, .a, .b] ++
        shadowLabelWordPower [.c, .b, .a, .b] (m + 2) := by
  rw [peripheralLong₅, List.map_flatMap,
    show m + 3 = (m + 2) + 1 by omega,
    List.range_succ_eq_map, List.flatMap_cons,
    List.flatMap_map]
  simp [peripheralLong₅Entry, cellSideBoundaryLabel_eq]
  rw [flatMap_range_const_word]
  rw [show m + 2 = (m + 1) + 1 by omega,
    shadowLabelWordPower_succ, shadowLabelWordPower_succ]
  simp [List.append_assoc]

def literalReducedPeripheralClockwiseLabels (m : ℕ) :
    List ShadowLabel :=
  [.c, .a, .c] ++ [.a, .c, .a] ++
    shadowLabelWordPower [.b, .a, .c, .a] (m + 2) ++
    [.b, .c, .b] ++ [.c, .b, .c] ++
    shadowLabelWordPower [.a, .c, .b, .c] (m + 2) ++
    [.a, .b, .a] ++ [.b, .a, .b] ++
    shadowLabelWordPower [.c, .b, .a, .b] (m + 2)

theorem literalPeripheralIncidences_labels (m : ℕ) :
    (literalPeripheralIncidences m).map cellSideBoundaryLabel =
      literalReducedPeripheralClockwiseLabels m := by
  simp only [literalPeripheralIncidences, List.map_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.map_cons, List.map_nil, cellSideBoundaryLabel_eq,
    peripheralLong₁_labels, peripheralLong₃_labels,
    peripheralLong₅_labels, literalReducedPeripheralClockwiseLabels]
  simp [List.append_assoc]

theorem labeledEdgeWord_literalReducedPeripheralBoundary (m : ℕ) :
    labeledEdgeWord (literalReducedPeripheralBoundary m) =
      (literalReducedPeripheralClockwiseLabels m).reverse := by
  simp only [labeledEdgeWord, literalReducedPeripheralBoundary,
    List.map_map, List.map_reverse]
  rw [← literalPeripheralIncidences_labels]
  rfl

end BenzelProblem6Kernel
