import BenzelProblem6Kernel.PeripheralIncidenceNodup

/-! # Exact length of the reduced peripheral boundary -/

namespace BenzelProblem6Kernel

theorem sum_range_succ_three_else_four (count : ℕ) :
    ((List.range (count + 1)).map
      (fun r => if r = 0 then 3 else 4)).sum = 3 + 4 * count := by
  induction count with
  | zero => decide
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        List.range_succ, List.map_append, List.sum_append, ih]
      simp
      omega

theorem peripheralLong₁_length (m : ℕ) :
    (peripheralLong₁ m).length = 4 * m + 11 := by
  rw [peripheralLong₁, List.length_flatMap]
  have hsum := sum_range_succ_three_else_four (m + 2)
  rw [show m + 3 = (m + 2) + 1 by omega]
  have hmap :
      (List.range (m + 2 + 1)).map
        (List.length ∘ peripheralLong₁Entry m) =
      (List.range (m + 2 + 1)).map
        (fun r => if r = 0 then 3 else 4) := by
    apply List.map_congr_left
    intro r hr
    by_cases h : r = 0 <;> simp [peripheralLong₁Entry, h]
  rw [hmap, hsum]
  omega

theorem peripheralLong₃_length (m : ℕ) :
    (peripheralLong₃ m).length = 4 * m + 11 := by
  rw [peripheralLong₃, List.length_flatMap]
  have hsum := sum_range_succ_three_else_four (m + 2)
  rw [show m + 3 = (m + 2) + 1 by omega]
  have hmap :
      (List.range (m + 2 + 1)).map
        (List.length ∘ peripheralLong₃Entry m) =
      (List.range (m + 2 + 1)).map
        (fun r => if r = 0 then 3 else 4) := by
    apply List.map_congr_left
    intro r hr
    by_cases h : r = 0 <;> simp [peripheralLong₃Entry, h]
  rw [hmap, hsum]
  omega

theorem peripheralLong₅_length (m : ℕ) :
    (peripheralLong₅ m).length = 4 * m + 11 := by
  rw [peripheralLong₅, List.length_flatMap]
  have hsum := sum_range_succ_three_else_four (m + 2)
  rw [show m + 3 = (m + 2) + 1 by omega]
  have hmap :
      (List.range (m + 2 + 1)).map
        (List.length ∘ peripheralLong₅Entry m) =
      (List.range (m + 2 + 1)).map
        (fun r => if r = 0 then 3 else 4) := by
    apply List.map_congr_left
    intro r hr
    by_cases h : r = 0 <;> simp [peripheralLong₅Entry, h]
  rw [hmap, hsum]
  omega

theorem literalPeripheralIncidences_length (m : ℕ) :
    (literalPeripheralIncidences m).length = 12 * m + 42 := by
  simp only [literalPeripheralIncidences, List.length_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.length_cons, List.length_nil,
    peripheralLong₁_length, peripheralLong₃_length,
    peripheralLong₅_length]
  omega

theorem literalReducedPeripheralBoundary_length (m : ℕ) :
    (literalReducedPeripheralBoundary m).length = 12 * m + 42 := by
  rw [literalReducedPeripheralBoundary, List.length_map,
    List.length_reverse, literalPeripheralIncidences_length]

end BenzelProblem6Kernel
