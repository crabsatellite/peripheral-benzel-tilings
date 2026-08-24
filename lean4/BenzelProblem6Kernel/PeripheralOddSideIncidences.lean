import BenzelProblem6Kernel.PeripheralEvenSideIncidences

/-! # Side-one and side-three slices of the peripheral incidence list -/

namespace BenzelProblem6Kernel

def literalPeripheralSide₁Incidences (m : ℕ) : List CellSide :=
  (literalPeripheralIncidences m).filter
    (fun datum => datum.2 == HexSide.side₁)

def explicitPeripheralSide₁Incidences (m : ℕ) : List CellSide :=
  (List.range (m + 3)).flatMap (fun r =>
    if r = 0 then [] else
      [((-(r : ℤ), -((m : ℤ)) + 2 * r - 3), .side₁)]) ++
  [((-((m : ℤ)) - 3, (m : ℤ) + 3), .side₁),
    ((-((m : ℤ)) - 2, (m : ℤ) + 3), .side₁)] ++
  (List.range (m + 3)).flatMap (fun r =>
    [((-((m : ℤ)) + 2 * r - 1, (m : ℤ) - r + 3), .side₁)])

theorem filter_peripheralLong₁_side₁ (m : ℕ) :
    (peripheralLong₁ m).filter
        (fun datum => datum.2 == HexSide.side₁) = [] := by
  simp [peripheralLong₁, List.filter_flatMap,
    peripheralLong₁Entry]

theorem filter_peripheralLong₃_side₁ (m : ℕ) :
    (peripheralLong₃ m).filter
        (fun datum => datum.2 == HexSide.side₁) =
      (List.range (m + 3)).flatMap (fun r =>
        if r = 0 then [] else
          [((-(r : ℤ), -((m : ℤ)) + 2 * r - 3), .side₁)]) := by
  rw [peripheralLong₃, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  by_cases h : r = 0 <;> simp [peripheralLong₃Entry, h]

theorem filter_peripheralLong₅_side₁ (m : ℕ) :
    (peripheralLong₅ m).filter
        (fun datum => datum.2 == HexSide.side₁) =
      (List.range (m + 3)).flatMap (fun r =>
        [((-((m : ℤ)) + 2 * r - 1, (m : ℤ) - r + 3), .side₁)]) := by
  rw [peripheralLong₅, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  by_cases h : r = 0 <;> simp [peripheralLong₅Entry, h]

theorem literalPeripheralSide₁Incidences_eq_explicit (m : ℕ) :
    literalPeripheralSide₁Incidences m =
      explicitPeripheralSide₁Incidences m := by
  simp only [literalPeripheralSide₁Incidences,
    literalPeripheralIncidences, List.filter_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.filter_cons, List.filter_nil]
  rw [filter_peripheralLong₁_side₁, filter_peripheralLong₃_side₁,
    filter_peripheralLong₅_side₁]
  simp [explicitPeripheralSide₁Incidences, List.append_assoc]

set_option maxRecDepth 4000 in
theorem literalPeripheralSide₁Incidences_nodup (m : ℕ) :
    (literalPeripheralSide₁Incidences m).Nodup := by
  rw [literalPeripheralSide₁Incidences_eq_explicit]
  let first : List CellSide :=
    (List.range (m + 3)).flatMap (fun r =>
      if r = 0 then [] else
        [((-(r : ℤ), -((m : ℤ)) + 2 * r - 3), .side₁)])
  let fixed : List CellSide :=
    [((-((m : ℤ)) - 3, (m : ℤ) + 3), .side₁),
      ((-((m : ℤ)) - 2, (m : ℤ) + 3), .side₁)]
  let last : List CellSide :=
    (List.range (m + 3)).flatMap (fun r =>
      [((-((m : ℤ)) + 2 * r - 1, (m : ℤ) - r + 3), .side₁)])
  have hperm : List.Perm (first ++ fixed ++ last)
      (fixed ++ first ++ last) := by
    exact (List.perm_append_comm.append_right last)
  apply hperm.nodup_iff.mpr
  dsimp [first, fixed, last]
  simp [List.nodup_append, List.nodup_flatMap,
    List.pairwise_append, List.disjoint_left, Function.onFun]
  constructor
  · constructor
    · intro r hr hr0 hfirst hsecond
      omega
    · intro r hr hfirst hsecond
      omega
  · constructor
    · constructor
      · intro r hr hr0 hfirst hsecond
        omega
      · intro r hr hfirst hsecond
        omega
    · constructor
      · constructor
        · intro r hr
          by_cases hr0 : r = 0 <;> simp [hr0]
        · apply (List.pairwise_lt_range (m + 3)).imp
          intro r s hrs
          by_cases hr : r = 0 <;> by_cases hs : s = 0
          all_goals simp [Function.onFun, List.disjoint_left, hr, hs]
          all_goals omega
      · constructor
        · apply (List.pairwise_lt_range (m + 3)).imp
          intro r s hrs
          simp [Function.onFun, List.disjoint_left]
          omega
        · intro a b side r hr hr0 ha hb hside s hs ha' hb' hside'
          subst side
          omega

def literalPeripheralSide₃Incidences (m : ℕ) : List CellSide :=
  (literalPeripheralIncidences m).filter
    (fun datum => datum.2 == HexSide.side₃)

def explicitPeripheralSide₃Incidences (m : ℕ) : List CellSide :=
  (List.range (m + 3)).flatMap (fun r =>
    if r = 0 then [] else
      [(((m : ℤ) - r + 4, -(r : ℤ)), .side₃)]) ++
  [((1, -((m : ℤ)) - 3), .side₃),
    ((0, -((m : ℤ)) - 2), .side₃)] ++
  (List.range (m + 3)).flatMap (fun r =>
    [((-(r : ℤ) - 1, -((m : ℤ)) + 2 * r - 1), .side₃)])

theorem filter_peripheralLong₁_side₃ (m : ℕ) :
    (peripheralLong₁ m).filter
        (fun datum => datum.2 == HexSide.side₃) =
      (List.range (m + 3)).flatMap (fun r =>
        if r = 0 then [] else
          [(((m : ℤ) - r + 4, -(r : ℤ)), .side₃)]) := by
  rw [peripheralLong₁, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  by_cases h : r = 0 <;> simp [peripheralLong₁Entry, h]

theorem filter_peripheralLong₃_side₃ (m : ℕ) :
    (peripheralLong₃ m).filter
        (fun datum => datum.2 == HexSide.side₃) =
      (List.range (m + 3)).flatMap (fun r =>
        [((-(r : ℤ) - 1, -((m : ℤ)) + 2 * r - 1), .side₃)]) := by
  rw [peripheralLong₃, List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  by_cases h : r = 0 <;> simp [peripheralLong₃Entry, h]

theorem filter_peripheralLong₅_side₃ (m : ℕ) :
    (peripheralLong₅ m).filter
        (fun datum => datum.2 == HexSide.side₃) = [] := by
  simp [peripheralLong₅, List.filter_flatMap,
    peripheralLong₅Entry]

theorem literalPeripheralSide₃Incidences_eq_explicit (m : ℕ) :
    literalPeripheralSide₃Incidences m =
      explicitPeripheralSide₃Incidences m := by
  simp only [literalPeripheralSide₃Incidences,
    literalPeripheralIncidences, List.filter_append,
    peripheralFixed₀, peripheralFixed₂, peripheralFixed₄,
    List.filter_cons, List.filter_nil]
  rw [filter_peripheralLong₁_side₃, filter_peripheralLong₃_side₃,
    filter_peripheralLong₅_side₃]
  simp [explicitPeripheralSide₃Incidences, List.append_assoc]

set_option maxRecDepth 4000 in
theorem literalPeripheralSide₃Incidences_nodup (m : ℕ) :
    (literalPeripheralSide₃Incidences m).Nodup := by
  rw [literalPeripheralSide₃Incidences_eq_explicit]
  let first : List CellSide :=
    (List.range (m + 3)).flatMap (fun r =>
      if r = 0 then [] else
        [(((m : ℤ) - r + 4, -(r : ℤ)), .side₃)])
  let fixed : List CellSide :=
    [((1, -((m : ℤ)) - 3), .side₃),
      ((0, -((m : ℤ)) - 2), .side₃)]
  let last : List CellSide :=
    (List.range (m + 3)).flatMap (fun r =>
      [((-(r : ℤ) - 1, -((m : ℤ)) + 2 * r - 1), .side₃)])
  have hperm : List.Perm (first ++ fixed ++ last)
      (fixed ++ first ++ last) := by
    exact (List.perm_append_comm.append_right last)
  apply hperm.nodup_iff.mpr
  dsimp [first, fixed, last]
  simp [List.nodup_append, List.nodup_flatMap,
    List.pairwise_append, List.disjoint_left, Function.onFun]
  constructor
  · constructor
    · intro r hr hr0 hfirst hsecond
      omega
    · intro r hr hfirst hsecond
      omega
  · constructor
    · constructor
      · intro r hr hr0 hfirst hsecond
        omega
      · intro r hr hfirst hsecond
        omega
    · constructor
      · constructor
        · intro r hr
          by_cases hr0 : r = 0 <;> simp [hr0]
        · apply (List.pairwise_lt_range (m + 3)).imp
          intro r s hrs
          by_cases hr : r = 0 <;> by_cases hs : s = 0
          all_goals simp [Function.onFun, List.disjoint_left, hr, hs]
          all_goals omega
      · constructor
        · apply (List.pairwise_lt_range (m + 3)).imp
          intro r s hrs
          simp [Function.onFun, List.disjoint_left]
          omega
        · intro a b side r hr hr0 ha hb hside s hs ha' hb' hside'
          subst side
          omega

end BenzelProblem6Kernel
