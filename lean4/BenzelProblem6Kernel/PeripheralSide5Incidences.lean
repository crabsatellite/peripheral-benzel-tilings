import BenzelProblem6Kernel.HexCellDirectedEdgeIncidence

/-! # The side-five slice of the explicit peripheral incidence list -/

namespace BenzelProblem6Kernel

instance isInsidePeripheralEdgeDecidable (m : ℕ)
    (cell : Cell) (side : HexSide) :
    Decidable (IsInsidePeripheralEdge m cell side) := by
  unfold IsInsidePeripheralEdge
  infer_instance

def literalPeripheralSide₅Incidences (m : ℕ) : List CellSide :=
  (literalPeripheralIncidences m).filter
    (fun datum => datum.2 == HexSide.side₅)

theorem filter_peripheralLong₁_side₅ (m : ℕ) :
    (peripheralLong₁ m).filter
        (fun datum => datum.2 == HexSide.side₅) =
      (List.range (m + 3)).flatMap fun r =>
        [(((m : ℤ) - r + 3, -(r : ℤ) - 1), HexSide.side₅)] := by
  rw [peripheralLong₁, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  simp [peripheralLong₁Entry]

theorem filter_peripheralLong₃_side₅ (m : ℕ) :
    (peripheralLong₃ m).filter
        (fun datum => datum.2 == HexSide.side₅) = [] := by
  simp [peripheralLong₃, List.filter_flatMap,
    peripheralLong₃Entry]

theorem filter_peripheralLong₅_side₅ (m : ℕ) :
    (peripheralLong₅ m).filter
        (fun datum => datum.2 == HexSide.side₅) =
      (List.range (m + 3)).flatMap fun r =>
        if r = 0 then [] else
          [((-((m : ℤ)) + 2 * r - 3, (m : ℤ) - r + 4),
            HexSide.side₅)] := by
  rw [peripheralLong₅, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  simp [peripheralLong₅Entry]

def explicitPeripheralSide₅Incidences (m : ℕ) : List CellSide :=
  [(((m : ℤ) + 3, 1), .side₅),
    (((m : ℤ) + 3, 0), .side₅)] ++
  (List.range (m + 3)).flatMap (fun r =>
    [(((m : ℤ) - r + 3, -(r : ℤ) - 1), .side₅)]) ++
  (List.range (m + 3)).flatMap (fun r =>
    if r = 0 then [] else
      [((-((m : ℤ)) + 2 * r - 3, (m : ℤ) - r + 4), .side₅)])

theorem literalPeripheralSide₅Incidences_eq_explicit (m : ℕ) :
    literalPeripheralSide₅Incidences m =
      explicitPeripheralSide₅Incidences m := by
  simp only [literalPeripheralSide₅Incidences,
    literalPeripheralIncidences, List.filter_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.filter_cons, List.filter_nil]
  rw [filter_peripheralLong₁_side₅,
    filter_peripheralLong₃_side₅,
    filter_peripheralLong₅_side₅]
  simp [explicitPeripheralSide₅Incidences, List.append_assoc]

theorem literalPeripheralSide₅Incidences_nodup (m : ℕ) :
    (literalPeripheralSide₅Incidences m).Nodup := by
  rw [literalPeripheralSide₅Incidences_eq_explicit]
  simp [explicitPeripheralSide₅Incidences,
    List.nodup_flatMap, List.pairwise_append, List.disjoint_left,
    Function.onFun]
  aesop (config := { warnOnNonterminal := false })
  all_goals try omega
  simp [List.nodup_append, List.nodup_flatMap, List.pairwise_append,
    List.disjoint_left, Function.onFun]
  aesop (config := { warnOnNonterminal := false })
  all_goals try omega
  · apply (List.pairwise_lt_range (m + 3)).imp
    intro r s hrs
    simp [Function.onFun, List.disjoint_left]
    omega
  · apply (List.pairwise_lt_range (m + 3)).imp
    intro r s hrs
    by_cases hr : r = 0 <;> by_cases hs : s = 0
    all_goals simp [Function.onFun, List.disjoint_left, hr, hs]
    all_goals omega

end BenzelProblem6Kernel
