import BenzelProblem6Kernel.PeripheralSide2Incidences

/-! # Side-zero and side-four slices of the peripheral incidence list -/

namespace BenzelProblem6Kernel

def literalPeripheralSide₀Incidences (m : ℕ) : List CellSide :=
  (literalPeripheralIncidences m).filter
    (fun datum => datum.2 == HexSide.side₀)

def explicitPeripheralSide₀Incidences (m : ℕ) : List CellSide :=
  [((-((m : ℤ)) - 3, (m : ℤ) + 3), .side₀)] ++
  (List.range (m + 3)).flatMap (fun r =>
    [((-((m : ℤ)) + 2 * r - 2, (m : ℤ) - r + 3), .side₀),
      ((-((m : ℤ)) + 2 * r - 1, (m : ℤ) - r + 3), .side₀)])

theorem filter_peripheralLong₁_side₀ (m : ℕ) :
    (peripheralLong₁ m).filter
        (fun datum => datum.2 == HexSide.side₀) = [] := by
  simp [peripheralLong₁, List.filter_flatMap,
    peripheralLong₁Entry]

theorem filter_peripheralLong₃_side₀ (m : ℕ) :
    (peripheralLong₃ m).filter
        (fun datum => datum.2 == HexSide.side₀) = [] := by
  simp [peripheralLong₃, List.filter_flatMap,
    peripheralLong₃Entry]

theorem filter_peripheralLong₅_side₀ (m : ℕ) :
    (peripheralLong₅ m).filter
        (fun datum => datum.2 == HexSide.side₀) =
      (List.range (m + 3)).flatMap (fun r =>
        [((-((m : ℤ)) + 2 * r - 2, (m : ℤ) - r + 3), .side₀),
          ((-((m : ℤ)) + 2 * r - 1, (m : ℤ) - r + 3), .side₀)]) := by
  rw [peripheralLong₅, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  by_cases h : r = 0 <;> simp [peripheralLong₅Entry, h]

theorem literalPeripheralSide₀Incidences_eq_explicit (m : ℕ) :
    literalPeripheralSide₀Incidences m =
      explicitPeripheralSide₀Incidences m := by
  simp only [literalPeripheralSide₀Incidences,
    literalPeripheralIncidences, List.filter_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.filter_cons, List.filter_nil]
  rw [filter_peripheralLong₁_side₀, filter_peripheralLong₃_side₀,
    filter_peripheralLong₅_side₀]
  simp [explicitPeripheralSide₀Incidences, List.append_assoc]

theorem literalPeripheralSide₀Incidences_nodup (m : ℕ) :
    (literalPeripheralSide₀Incidences m).Nodup := by
  rw [literalPeripheralSide₀Incidences_eq_explicit]
  simp [explicitPeripheralSide₀Incidences,
    List.nodup_flatMap, List.pairwise_append, List.disjoint_left,
    Function.onFun]
  constructor
  · intro r hr
    constructor <;> omega
  · apply (List.pairwise_lt_range (m + 3)).imp
    intro r s hrs
    simp [Function.onFun, List.disjoint_left]
    omega

def literalPeripheralSide₄Incidences (m : ℕ) : List CellSide :=
  (literalPeripheralIncidences m).filter
    (fun datum => datum.2 == HexSide.side₄)

def explicitPeripheralSide₄Incidences (m : ℕ) : List CellSide :=
  [(((m : ℤ) + 3, 1), .side₄)] ++
  (List.range (m + 3)).flatMap (fun r =>
    [(((m : ℤ) - r + 3, -(r : ℤ)), .side₄),
      (((m : ℤ) - r + 3, -(r : ℤ) - 1), .side₄)])

theorem filter_peripheralLong₁_side₄ (m : ℕ) :
    (peripheralLong₁ m).filter
        (fun datum => datum.2 == HexSide.side₄) =
      (List.range (m + 3)).flatMap (fun r =>
        [(((m : ℤ) - r + 3, -(r : ℤ)), .side₄),
          (((m : ℤ) - r + 3, -(r : ℤ) - 1), .side₄)]) := by
  rw [peripheralLong₁, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  by_cases h : r = 0 <;> simp [peripheralLong₁Entry, h]

theorem filter_peripheralLong₃_side₄ (m : ℕ) :
    (peripheralLong₃ m).filter
        (fun datum => datum.2 == HexSide.side₄) = [] := by
  simp [peripheralLong₃, List.filter_flatMap,
    peripheralLong₃Entry]

theorem filter_peripheralLong₅_side₄ (m : ℕ) :
    (peripheralLong₅ m).filter
        (fun datum => datum.2 == HexSide.side₄) = [] := by
  simp [peripheralLong₅, List.filter_flatMap,
    peripheralLong₅Entry]

theorem literalPeripheralSide₄Incidences_eq_explicit (m : ℕ) :
    literalPeripheralSide₄Incidences m =
      explicitPeripheralSide₄Incidences m := by
  simp only [literalPeripheralSide₄Incidences,
    literalPeripheralIncidences, List.filter_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.filter_cons, List.filter_nil]
  rw [filter_peripheralLong₁_side₄, filter_peripheralLong₃_side₄,
    filter_peripheralLong₅_side₄]
  simp [explicitPeripheralSide₄Incidences, List.append_assoc]

theorem literalPeripheralSide₄Incidences_nodup (m : ℕ) :
    (literalPeripheralSide₄Incidences m).Nodup := by
  rw [literalPeripheralSide₄Incidences_eq_explicit]
  simp [explicitPeripheralSide₄Incidences,
    List.nodup_flatMap, List.pairwise_append, List.disjoint_left,
    Function.onFun]
  constructor
  · intro r hr
    constructor <;> omega
  · constructor
    · intro r hr
      omega
    · apply (List.pairwise_lt_range (m + 3)).imp
      intro r s hrs
      simp [Function.onFun, List.disjoint_left]
      omega

end BenzelProblem6Kernel
