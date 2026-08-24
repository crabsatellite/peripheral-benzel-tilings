import BenzelProblem6Kernel.PeripheralSide5Incidences

/-! # The side-two slice of the explicit peripheral incidence list -/

namespace BenzelProblem6Kernel

def literalPeripheralSide₂Incidences (m : ℕ) : List CellSide :=
  (literalPeripheralIncidences m).filter
    (fun datum => datum.2 == HexSide.side₂)

def explicitPeripheralSide₂Incidences (m : ℕ) : List CellSide :=
  [((1, -((m : ℤ)) - 3), .side₂)] ++
  (List.range (m + 3)).flatMap (fun r =>
    [((-(r : ℤ), -((m : ℤ)) + 2 * r - 2), .side₂),
      ((-(r : ℤ) - 1, -((m : ℤ)) + 2 * r - 1), .side₂)])

theorem filter_peripheralLong₁_side₂ (m : ℕ) :
    (peripheralLong₁ m).filter
        (fun datum => datum.2 == HexSide.side₂) = [] := by
  simp [peripheralLong₁, List.filter_flatMap,
    peripheralLong₁Entry]

theorem filter_peripheralLong₃_side₂ (m : ℕ) :
    (peripheralLong₃ m).filter
        (fun datum => datum.2 == HexSide.side₂) =
      (List.range (m + 3)).flatMap (fun r =>
        [((-(r : ℤ), -((m : ℤ)) + 2 * r - 2), .side₂),
          ((-(r : ℤ) - 1, -((m : ℤ)) + 2 * r - 1), .side₂)]) := by
  rw [peripheralLong₃, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  simp [peripheralLong₃Entry]

theorem filter_peripheralLong₅_side₂ (m : ℕ) :
    (peripheralLong₅ m).filter
        (fun datum => datum.2 == HexSide.side₂) = [] := by
  simp [peripheralLong₅, List.filter_flatMap,
    peripheralLong₅Entry]

theorem literalPeripheralSide₂Incidences_eq_explicit (m : ℕ) :
    literalPeripheralSide₂Incidences m =
      explicitPeripheralSide₂Incidences m := by
  simp only [literalPeripheralSide₂Incidences,
    literalPeripheralIncidences, List.filter_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.filter_cons, List.filter_nil]
  rw [filter_peripheralLong₁_side₂,
    filter_peripheralLong₃_side₂,
    filter_peripheralLong₅_side₂]
  simp [explicitPeripheralSide₂Incidences, List.append_assoc]

theorem literalPeripheralSide₂Incidences_nodup (m : ℕ) :
    (literalPeripheralSide₂Incidences m).Nodup := by
  rw [literalPeripheralSide₂Incidences_eq_explicit]
  simp [explicitPeripheralSide₂Incidences,
    List.nodup_flatMap, List.pairwise_append, List.disjoint_left,
    Function.onFun]
  constructor
  · intro r hr
    constructor <;> omega
  · apply (List.pairwise_lt_range (m + 3)).imp
    intro r s hrs
    simp [Function.onFun, List.disjoint_left]
    omega

end BenzelProblem6Kernel
