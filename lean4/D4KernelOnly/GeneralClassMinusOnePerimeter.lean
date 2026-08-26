import D4KernelOnly.GeneralClassMinusOneSpurReduction

/-! # Exact perimeter support and reduced-boundary length -/

namespace FiniteDefects

open BenzelProblem6Kernel

def cmoCPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  (cmoSideFiveCells s r).map (fun cell =>
    cellBoundaryEdgeAt cell .side₅) ++
  (cmoSideFiveNegativeCells s r).map (fun cell =>
    reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅))

def cmoBPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  (cmoCPerimeterEdges s r).map d4RotateEdge

def cmoAPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  (cmoBPerimeterEdges s r).map d4RotateEdge

def cmoPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  cmoCPerimeterEdges s r ++ cmoBPerimeterEdges s r ++
    cmoAPerimeterEdges s r

theorem cmoCPerimeterEdges_nodup (s r : ℕ) :
    (cmoCPerimeterEdges s r).Nodup := by
  rw [cmoCPerimeterEdges, List.nodup_append]
  refine ⟨(cmoSideFiveCells_nodup s r).map
      cellBoundaryEdgeAt_sideFive_injective,
    (cmoSideFiveNegativeCells_nodup s r).map
      reverse_cellBoundaryEdgeAt_sideFive_injective, ?_⟩
  rw [List.disjoint_left]
  intro edge hpositive hnegative
  obtain ⟨positive, hpositiveCell, hpositiveEq⟩ := List.mem_map.mp hpositive
  obtain ⟨negative, hnegativeCell, hnegativeEq⟩ := List.mem_map.mp hnegative
  have hneighbor := cellBoundaryEdgeAt_neighbor_exact negative .side₅
  simp only [oppositeHexSide] at hneighbor
  have hedge : cellBoundaryEdgeAt (neighboringCell negative .side₅) .side₂ =
      cellBoundaryEdgeAt positive .side₅ := by
    rw [hneighbor, hnegativeEq, ← hpositiveEq]
  have hsides :=
    (cellBoundaryEdgeAt_eq_iff positive
      (neighboringCell negative .side₅) .side₅ .side₂).mp hedge |>.2
  exact (by cases hsides)

theorem cmoBPerimeterEdges_nodup (s r : ℕ) :
    (cmoBPerimeterEdges s r).Nodup :=
  (cmoCPerimeterEdges_nodup s r).map d4RotateEdge_injective

theorem cmoAPerimeterEdges_nodup (s r : ℕ) :
    (cmoAPerimeterEdges s r).Nodup :=
  (cmoBPerimeterEdges_nodup s r).map d4RotateEdge_injective

theorem cmoCPerimeterEdges_label (s r : ℕ) {edge : LabeledHexEdge}
    (hedge : edge ∈ cmoCPerimeterEdges s r) : edge.label = .c := by
  simp only [cmoCPerimeterEdges, List.mem_append, List.mem_map] at hedge
  rcases hedge with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩ <;> rfl

theorem cmoBPerimeterEdges_label (s r : ℕ) {edge : LabeledHexEdge}
    (hedge : edge ∈ cmoBPerimeterEdges s r) : edge.label = .b := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hedge
  change d4RotateLabel source.label = .b
  rw [show source.label = .c from cmoCPerimeterEdges_label s r hsource]
  rfl

theorem cmoAPerimeterEdges_label (s r : ℕ) {edge : LabeledHexEdge}
    (hedge : edge ∈ cmoAPerimeterEdges s r) : edge.label = .a := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hedge
  change d4RotateLabel source.label = .a
  rw [show source.label = .b from cmoBPerimeterEdges_label s r hsource]
  rfl

theorem cmoPerimeterEdges_nodup (s r : ℕ) :
    (cmoPerimeterEdges s r).Nodup := by
  rw [cmoPerimeterEdges, List.nodup_append]
  constructor
  · rw [List.nodup_append]
    refine ⟨cmoCPerimeterEdges_nodup s r,
      cmoBPerimeterEdges_nodup s r, ?_⟩
    rw [List.disjoint_left]
    intro edge hc hb
    have hcLabel := cmoCPerimeterEdges_label s r hc
    have hbLabel := cmoBPerimeterEdges_label s r hb
    cases hcLabel.symm.trans hbLabel
  · constructor
    · exact cmoAPerimeterEdges_nodup s r
    · rw [List.disjoint_left]
      intro edge hcb ha
      rw [List.mem_append] at hcb
      have haLabel := cmoAPerimeterEdges_label s r ha
      rcases hcb with hc | hb
      · have hcLabel := cmoCPerimeterEdges_label s r hc
        cases hcLabel.symm.trans haLabel
      · have hbLabel := cmoBPerimeterEdges_label s r hb
        cases hbLabel.symm.trans haLabel

theorem cmoSideFiveCells_length (s r : ℕ) :
    (cmoSideFiveCells s r).length = 2 * (s + r) := by
  simp [cmoSideFiveCells, cmoPositiveFamily0, cmoPositiveFamily1,
    cmoPositiveFamily2, List.length_flatMap, Function.comp_def]
  omega

theorem cmoSideFiveNegativeCells_length
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoSideFiveNegativeCells s r).length = 2 * (s + r) := by
  simp [cmoSideFiveNegativeCells, cmoNegativeFamily0,
    cmoNegativeFamily1, cmoNegativeFamily2, cmoNegativeFamily3,
    List.length_flatMap, Function.comp_def]
  omega

theorem cmoCPerimeterEdges_length
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoCPerimeterEdges s r).length = 4 * (s + r) := by
  simp [cmoCPerimeterEdges, List.length_append,
    cmoSideFiveCells_length, cmoSideFiveNegativeCells_length s r hs]
  omega

theorem cmoPerimeterEdges_length
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoPerimeterEdges s r).length = 12 * (s + r) := by
  simp [cmoPerimeterEdges, cmoBPerimeterEdges, cmoAPerimeterEdges,
    List.length_append, cmoCPerimeterEdges_length s r hs]
  omega

theorem directedEdgeCoefficient_cmoReducedBoundary_allSides
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 1) (3 * s + 1)))
        (cellBoundaryEdgeAt cell side) :=
  ((reduceGeometricBacktracks_same_chain
    (classMinusOneLiteralBoundaryWalk s r))
      (cellBoundaryEdgeAt cell side)).symm.trans
        (directedEdgeCoefficient_classMinusOneBoundary_allSides
          s r hs cell side)

theorem cmoReducedCoefficient_positiveSideFive
    (s r : ℕ) (hs : 1 ≤ s) {cell : Cell}
    (hcell : cell ∈ cmoSideFiveCells s r) :
    directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
      (cellBoundaryEdgeAt cell .side₅) = 1 := by
  rw [directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs,
    offsetCellBoundaryCoefficient]
  have hgeometry := (mem_cmoSideFiveCells_iff s r hs cell).1 hcell
  have hp := classMinusOneOffsetParameters s r hs
  rw [hp.1, hp.2]
  simp [hgeometry.1, hgeometry.2]

theorem cmoReducedCoefficient_negativeSideFive
    (s r : ℕ) (hs : 1 ≤ s) {cell : Cell}
    (hcell : cell ∈ cmoSideFiveNegativeCells s r) :
    directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
      (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) = 1 := by
  rw [directedEdgeCoefficient_reverse_target,
    directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs,
    offsetCellBoundaryCoefficient]
  have hgeometry :=
    (mem_cmoSideFiveNegativeCells_iff s r hs cell).1 hcell
  have hp := classMinusOneOffsetParameters s r hs
  rw [hp.1, hp.2]
  simp [hgeometry.1, hgeometry.2]

theorem cmoReducedCoefficient_rotateSideFive
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₅)) =
      directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [d4RotateEdge_cell_sideFive,
    directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs,
    directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs,
    cmoCellBoundaryCoefficient_rotate_sideFive]

theorem cmoReducedCoefficient_rotateTwiceSideFive
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
        (d4RotateEdge (d4RotateEdge (cellBoundaryEdgeAt cell .side₅))) =
      directedEdgeCoefficient (cmoReducedBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [d4RotateEdge_cell_sideFive, d4RotateEdge_cell_sideThree,
    directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs,
    directedEdgeCoefficient_cmoReducedBoundary_allSides s r hs,
    cmoCellBoundaryCoefficient_rotate_sideThree,
    cmoCellBoundaryCoefficient_rotate_sideFive]

theorem cmoPerimeterEdge_coefficient_one
    (s r : ℕ) (hs : 1 ≤ s) {edge : LabeledHexEdge}
    (hedge : edge ∈ cmoPerimeterEdges s r) :
    directedEdgeCoefficient (cmoReducedBoundaryWalk s r) edge = 1 := by
  rw [cmoPerimeterEdges, List.mem_append, List.mem_append] at hedge
  rcases hedge with (hc | hb) | ha
  · simp only [cmoCPerimeterEdges, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · exact cmoReducedCoefficient_positiveSideFive s r hs hcell
    · exact cmoReducedCoefficient_negativeSideFive s r hs hcell
  · rw [cmoBPerimeterEdges] at hb
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hb
    simp only [cmoCPerimeterEdges, List.mem_append, List.mem_map] at hsource
    rcases hsource with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · rw [cmoReducedCoefficient_rotateSideFive s r hs]
      exact cmoReducedCoefficient_positiveSideFive s r hs hcell
    · rw [d4RotateEdge_reverse, directedEdgeCoefficient_reverse_target,
        cmoReducedCoefficient_rotateSideFive s r hs]
      have hneg := cmoReducedCoefficient_negativeSideFive s r hs hcell
      rw [directedEdgeCoefficient_reverse_target] at hneg
      omega
  · rw [cmoAPerimeterEdges] at ha
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp ha
    rw [cmoBPerimeterEdges] at hsource
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hsource
    simp only [cmoCPerimeterEdges, List.mem_append, List.mem_map] at horiginal
    rcases horiginal with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · rw [cmoReducedCoefficient_rotateTwiceSideFive s r hs]
      exact cmoReducedCoefficient_positiveSideFive s r hs hcell
    · rw [d4RotateEdge_reverse, d4RotateEdge_reverse,
        directedEdgeCoefficient_reverse_target,
        cmoReducedCoefficient_rotateTwiceSideFive s r hs]
      have hneg := cmoReducedCoefficient_negativeSideFive s r hs hcell
      rw [directedEdgeCoefficient_reverse_target] at hneg
      omega

theorem cmoPerimeterEdges_subset_reduced
    (s r : ℕ) (hs : 1 ≤ s) :
    ∀ edge ∈ cmoPerimeterEdges s r,
      edge ∈ cmoReducedBoundaryWalk s r := by
  intro edge hedge
  exact edge_mem_of_directedEdgeCoefficient_eq_one _ _
    (cmoPerimeterEdge_coefficient_one s r hs hedge)

theorem cmoReducedBoundary_length_lower
    (s r : ℕ) (hs : 1 ≤ s) :
    12 * (s + r) ≤ (cmoReducedBoundaryWalk s r).length := by
  rw [← cmoPerimeterEdges_length s r hs,
    ← List.toFinset_card_of_nodup (cmoPerimeterEdges_nodup s r),
    ← List.toFinset_card_of_nodup (cmoReducedBoundary_nodup s r hs)]
  apply Finset.card_le_card
  intro edge hedge
  exact List.mem_toFinset.mpr
    (cmoPerimeterEdges_subset_reduced s r hs edge
      (List.mem_toFinset.mp hedge))

theorem cmoReducedBoundary_length
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoReducedBoundaryWalk s r).length = 12 * (s + r) :=
  Nat.le_antisymm (cmoReducedBoundary_length_le s r hs)
    (cmoReducedBoundary_length_lower s r hs)

theorem cmoPerimeterEdges_perm_reduced
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoPerimeterEdges s r).Perm (cmoReducedBoundaryWalk s r) := by
  have hsubset : (cmoPerimeterEdges s r).toFinset ⊆
      (cmoReducedBoundaryWalk s r).toFinset := by
    intro edge hedge
    exact List.mem_toFinset.mpr
      (cmoPerimeterEdges_subset_reduced s r hs edge
        (List.mem_toFinset.mp hedge))
  have hcard : (cmoReducedBoundaryWalk s r).toFinset.card ≤
      (cmoPerimeterEdges s r).toFinset.card := by
    rw [List.toFinset_card_of_nodup (cmoReducedBoundary_nodup s r hs),
      List.toFinset_card_of_nodup (cmoPerimeterEdges_nodup s r),
      cmoReducedBoundary_length s r hs,
      cmoPerimeterEdges_length s r hs]
  have hfinset := Finset.eq_of_subset_of_card_le hsubset hcard
  apply (List.perm_ext_iff_of_nodup
    (cmoPerimeterEdges_nodup s r)
    (cmoReducedBoundary_nodup s r hs)).mpr
  intro edge
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp hfinset edge

end FiniteDefects
