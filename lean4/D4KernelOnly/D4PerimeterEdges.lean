import D4KernelOnly.D4BoundarySpurReduction

/-! # Exact perimeter-edge support and reduced-boundary length -/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4CPerimeterEdges (m : ℕ) : List LabeledHexEdge :=
  (d4SideFiveCells m).map (fun cell =>
    cellBoundaryEdgeAt cell .side₅) ++
  (d4SideFiveNegativeCells m).map (fun cell =>
    reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅))

def d4BPerimeterEdges (m : ℕ) : List LabeledHexEdge :=
  (d4CPerimeterEdges m).map d4RotateEdge

def d4APerimeterEdges (m : ℕ) : List LabeledHexEdge :=
  (d4BPerimeterEdges m).map d4RotateEdge

def d4PerimeterEdges (m : ℕ) : List LabeledHexEdge :=
  d4CPerimeterEdges m ++ d4BPerimeterEdges m ++ d4APerimeterEdges m

theorem d4CPerimeterEdges_nodup (m : ℕ) :
    (d4CPerimeterEdges m).Nodup := by
  rw [d4CPerimeterEdges, List.nodup_append]
  refine ⟨(d4SideFiveCells_nodup m).map
      cellBoundaryEdgeAt_sideFive_injective,
    (d4SideFiveNegativeCells_nodup m).map
      reverse_cellBoundaryEdgeAt_sideFive_injective, ?_⟩
  rw [List.disjoint_left]
  intro edge hpositive hnegative
  obtain ⟨positive, hpositiveCell, hpositiveEq⟩ :=
    List.mem_map.mp hpositive
  obtain ⟨negative, hnegativeCell, hnegativeEq⟩ :=
    List.mem_map.mp hnegative
  have hneighbor := cellBoundaryEdgeAt_neighbor_exact negative .side₅
  simp only [oppositeHexSide] at hneighbor
  have hedge : cellBoundaryEdgeAt (neighboringCell negative .side₅) .side₂ =
      cellBoundaryEdgeAt positive .side₅ := by
    rw [hneighbor, hnegativeEq, ← hpositiveEq]
  have hsides :=
    (cellBoundaryEdgeAt_eq_iff positive
      (neighboringCell negative .side₅) .side₅ .side₂).mp hedge |>.2
  exact (by cases hsides)

theorem d4BPerimeterEdges_nodup (m : ℕ) :
    (d4BPerimeterEdges m).Nodup :=
  (d4CPerimeterEdges_nodup m).map d4RotateEdge_injective

theorem d4APerimeterEdges_nodup (m : ℕ) :
    (d4APerimeterEdges m).Nodup :=
  (d4BPerimeterEdges_nodup m).map d4RotateEdge_injective

theorem d4CPerimeterEdges_label (m : ℕ) {edge : LabeledHexEdge}
    (hedge : edge ∈ d4CPerimeterEdges m) : edge.label = .c := by
  simp only [d4CPerimeterEdges, List.mem_append, List.mem_map] at hedge
  rcases hedge with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩ <;> rfl

theorem d4BPerimeterEdges_label (m : ℕ) {edge : LabeledHexEdge}
    (hedge : edge ∈ d4BPerimeterEdges m) : edge.label = .b := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hedge
  change d4RotateLabel source.label = .b
  rw [show source.label = .c from d4CPerimeterEdges_label m hsource]
  rfl

theorem d4APerimeterEdges_label (m : ℕ) {edge : LabeledHexEdge}
    (hedge : edge ∈ d4APerimeterEdges m) : edge.label = .a := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hedge
  change d4RotateLabel source.label = .a
  rw [show source.label = .b from d4BPerimeterEdges_label m hsource]
  rfl

theorem d4PerimeterEdges_nodup (m : ℕ) :
    (d4PerimeterEdges m).Nodup := by
  rw [d4PerimeterEdges, List.nodup_append]
  constructor
  · rw [List.nodup_append]
    refine ⟨d4CPerimeterEdges_nodup m,
      d4BPerimeterEdges_nodup m, ?_⟩
    rw [List.disjoint_left]
    intro edge hc hb
    have hcLabel := d4CPerimeterEdges_label m hc
    have hbLabel := d4BPerimeterEdges_label m hb
    cases hcLabel.symm.trans hbLabel
  · constructor
    · exact d4APerimeterEdges_nodup m
    · rw [List.disjoint_left]
      intro edge hcb ha
      rw [List.mem_append] at hcb
      have haLabel := d4APerimeterEdges_label m ha
      rcases hcb with hc | hb
      · have hcLabel := d4CPerimeterEdges_label m hc
        cases hcLabel.symm.trans haLabel
      · have hbLabel := d4BPerimeterEdges_label m hb
        cases hbLabel.symm.trans haLabel

theorem d4SideFiveCells_length (m : ℕ) :
    (d4SideFiveCells m).length = 2 * m + 4 := by
  have hleft : ((List.range (m + 1)).map (fun r =>
      ((r : ℤ) + 2, (r : ℤ) - (m : ℤ) - 1))).length = m + 1 := by
    rw [List.length_map]
    simp [List.length_flatMap, Function.comp_def]
  have hright : ((List.range (m + 1)).map (fun r =>
      ((m : ℤ) - 2 * (r : ℤ), (r : ℤ) + 2))).length = m + 1 := by
    rw [List.length_map]
    simp [List.length_flatMap, Function.comp_def]
  rw [d4SideFiveCells, List.length_append, List.length_append,
    hleft, hright]
  simp only [List.length_cons, List.length_nil]
  omega

theorem d4SideFiveNegativeCells_length (m : ℕ) :
    (d4SideFiveNegativeCells m).length = 2 * m + 4 := by
  have hflat (items : List ℕ) :
      (items.flatMap fun r =>
        [(-((m : ℤ)) - 2 + (r : ℤ),
            (m : ℤ) + 1 - 2 * (r : ℤ)),
          (-((m : ℤ)) - 2 + (r : ℤ),
            (m : ℤ) - 2 * (r : ℤ))]).length = 2 * items.length := by
    induction items with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.flatMap_cons, List.length_append,
          List.length_cons, List.length_nil, ih]
        omega
  rw [d4SideFiveNegativeCells, List.length_append, hflat]
  simp only [List.length_range, List.length_cons, List.length_nil]
  omega

theorem d4CPerimeterEdges_length (m : ℕ) :
    (d4CPerimeterEdges m).length = 4 * m + 8 := by
  simp [d4CPerimeterEdges, List.length_append,
    d4SideFiveCells_length, d4SideFiveNegativeCells_length]
  omega

theorem d4PerimeterEdges_length (m : ℕ) :
    (d4PerimeterEdges m).length = 12 * m + 24 := by
  simp [d4PerimeterEdges, d4BPerimeterEdges, d4APerimeterEdges,
    List.length_append, d4CPerimeterEdges_length]
  omega

theorem directedEdgeCoefficient_d4ReducedBoundary_allSides
    (m : ℕ) (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient (d4ReducedBoundaryWalk m)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell side) := by
  exact ((reduceGeometricBacktracks_same_chain
    (d4LiteralBoundaryWalk m)) (cellBoundaryEdgeAt cell side)).symm.trans
      (directedEdgeCoefficient_d4LiteralBoundaryWalk_allSides m cell side)

theorem d4ReducedCoefficient_positiveSideFive
    (m : ℕ) {cell : Cell} (hcell : cell ∈ d4SideFiveCells m) :
    directedEdgeCoefficient (d4ReducedBoundaryWalk m)
      (cellBoundaryEdgeAt cell .side₅) = 1 := by
  rw [directedEdgeCoefficient_d4ReducedBoundary_allSides,
    directedEdgeCoefficient_d4CellBoundaries]
  have hgeometry := (mem_d4SideFiveCells_iff m cell).1 hcell
  simp [hgeometry.1, hgeometry.2]

theorem d4ReducedCoefficient_negativeSideFive
    (m : ℕ) {cell : Cell} (hcell : cell ∈ d4SideFiveNegativeCells m) :
    directedEdgeCoefficient (d4ReducedBoundaryWalk m)
      (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) = 1 := by
  rw [directedEdgeCoefficient_reverse_target,
    directedEdgeCoefficient_d4ReducedBoundary_allSides,
    directedEdgeCoefficient_d4CellBoundaries]
  have hgeometry := (mem_d4SideFiveNegativeCells_iff m cell).1 hcell
  simp [hgeometry.1, hgeometry.2]

theorem d4ReducedCoefficient_rotateSideFive
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (d4ReducedBoundaryWalk m)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₅)) =
      directedEdgeCoefficient (d4ReducedBoundaryWalk m)
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [d4RotateEdge_cell_sideFive,
    directedEdgeCoefficient_d4ReducedBoundary_allSides,
    directedEdgeCoefficient_d4ReducedBoundary_allSides,
    d4CellBoundaryCoefficient_rotate_sideFive]

theorem d4ReducedCoefficient_rotateTwiceSideFive
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (d4ReducedBoundaryWalk m)
        (d4RotateEdge (d4RotateEdge (cellBoundaryEdgeAt cell .side₅))) =
      directedEdgeCoefficient (d4ReducedBoundaryWalk m)
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [d4RotateEdge_cell_sideFive, d4RotateEdge_cell_sideThree,
    directedEdgeCoefficient_d4ReducedBoundary_allSides,
    directedEdgeCoefficient_d4ReducedBoundary_allSides,
    d4CellBoundaryCoefficient_rotate_sideThree,
    d4CellBoundaryCoefficient_rotate_sideFive]

theorem d4PerimeterEdge_coefficient_one (m : ℕ)
    {edge : LabeledHexEdge} (hedge : edge ∈ d4PerimeterEdges m) :
    directedEdgeCoefficient (d4ReducedBoundaryWalk m) edge = 1 := by
  rw [d4PerimeterEdges, List.mem_append, List.mem_append] at hedge
  rcases hedge with (hc | hb) | ha
  · simp only [d4CPerimeterEdges, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · exact d4ReducedCoefficient_positiveSideFive m hcell
    · exact d4ReducedCoefficient_negativeSideFive m hcell
  · rw [d4BPerimeterEdges] at hb
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hb
    simp only [d4CPerimeterEdges, List.mem_append, List.mem_map] at hsource
    rcases hsource with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · rw [d4ReducedCoefficient_rotateSideFive]
      exact d4ReducedCoefficient_positiveSideFive m hcell
    · rw [d4RotateEdge_reverse, directedEdgeCoefficient_reverse_target,
        d4ReducedCoefficient_rotateSideFive]
      have hneg := d4ReducedCoefficient_negativeSideFive m hcell
      rw [directedEdgeCoefficient_reverse_target] at hneg
      omega
  · rw [d4APerimeterEdges] at ha
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp ha
    rw [d4BPerimeterEdges] at hsource
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hsource
    simp only [d4CPerimeterEdges, List.mem_append, List.mem_map] at horiginal
    rcases horiginal with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · rw [d4ReducedCoefficient_rotateTwiceSideFive]
      exact d4ReducedCoefficient_positiveSideFive m hcell
    · rw [d4RotateEdge_reverse, d4RotateEdge_reverse,
        directedEdgeCoefficient_reverse_target,
        d4ReducedCoefficient_rotateTwiceSideFive]
      have hneg := d4ReducedCoefficient_negativeSideFive m hcell
      rw [directedEdgeCoefficient_reverse_target] at hneg
      omega

theorem d4PerimeterEdges_subset_reduced (m : ℕ) :
    ∀ edge ∈ d4PerimeterEdges m, edge ∈ d4ReducedBoundaryWalk m := by
  intro edge hedge
  exact edge_mem_of_directedEdgeCoefficient_eq_one _ _
    (d4PerimeterEdge_coefficient_one m hedge)

theorem d4ReducedBoundary_length_lower (m : ℕ) :
    12 * m + 24 ≤ (d4ReducedBoundaryWalk m).length := by
  rw [← d4PerimeterEdges_length m,
    ← List.toFinset_card_of_nodup (d4PerimeterEdges_nodup m),
    ← List.toFinset_card_of_nodup (d4ReducedBoundary_nodup m)]
  apply Finset.card_le_card
  intro edge hedge
  exact List.mem_toFinset.mpr
    (d4PerimeterEdges_subset_reduced m edge (List.mem_toFinset.mp hedge))

theorem d4ReducedBoundary_length (m : ℕ) :
    (d4ReducedBoundaryWalk m).length = 12 * m + 24 := by
  exact Nat.le_antisymm (d4ReducedBoundary_length_le m)
    (d4ReducedBoundary_length_lower m)

end FiniteDefects
