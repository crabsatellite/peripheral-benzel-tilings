import D4KernelOnly.GeneralClassZeroEuler
import D4KernelOnly.GeneralClassZeroNodup
import D4KernelOnly.D4ReducedPeelingBoundary

/-! # Reduced class-zero boundary and its exact perimeter support -/

namespace FiniteDefects

open BenzelProblem6Kernel

def czReducedBoundaryWalk (s r : ℕ) : List LabeledHexEdge :=
  reduceGeometricBacktracks (classZeroLiteralBoundaryWalk s r)

theorem czReducedBoundary_continuous (s r : ℕ) :
    ContinuousLabeledEdgePath (classZeroClockwiseRoot s r)
      (czReducedBoundaryWalk s r) (classZeroClockwiseRoot s r) :=
  reduceGeometricBacktracks_continuous (classZeroLiteralBoundary_continuous s r)

theorem czReducedBoundary_edges_alternate (s r : ℕ) :
    ∀ edge ∈ czReducedBoundaryWalk s r, AlternatesHexVertexClass edge := by
  intro edge hedge
  exact classZeroLiteralBoundaryWalk_edges_alternate s r edge
    ((reduceGeometricBacktracks_sublist _).subset hedge)

theorem czReducedBoundary_nodup (s r : ℕ) :
    (czReducedBoundaryWalk s r).Nodup :=
  (classZeroLiteralBoundaryWalk_nodup s r).sublist
    (reduceGeometricBacktracks_sublist _)

def czReducedRootedBoundary (s r : ℕ) : RootedAlternatingBoundary where
  edges := czReducedBoundaryWalk s r
  root := classZeroClockwiseRoot s r
  continuous := czReducedBoundary_continuous s r
  root_classZero := classZeroLiteralBoundaryRoot_classZero s r
  alternates := czReducedBoundary_edges_alternate s r

theorem directedEdgeCoefficient_czReducedBoundary_allSides
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (cell : Cell) (side : HexSide) :
    directedEdgeCoefficient (czReducedBoundaryWalk s r)
        (cellBoundaryEdgeAt cell side) =
      directedEdgeCoefficient
        (orientedCellBoundaryList
          (offsetCellValueList (2 * s + r - 2) (3 * s)))
        (cellBoundaryEdgeAt cell side) :=
  ((reduceGeometricBacktracks_same_chain (classZeroLiteralBoundaryWalk s r))
    (cellBoundaryEdgeAt cell side)).symm.trans
      (directedEdgeCoefficient_classZeroBoundary_allSides s r hs hr cell side)

def czCPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  (czSideFiveCells s r).map (fun cell => cellBoundaryEdgeAt cell .side₅) ++
    (czSideFiveNegativeCells s r).map (fun cell =>
      reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅))

def czBPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  (czCPerimeterEdges s r).map d4RotateEdge
def czAPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  (czBPerimeterEdges s r).map d4RotateEdge
def czPerimeterEdges (s r : ℕ) : List LabeledHexEdge :=
  czCPerimeterEdges s r ++ czBPerimeterEdges s r ++ czAPerimeterEdges s r

theorem czPositiveFamily0_nodup (s r : ℕ) : (czPositiveFamily0 s r).Nodup := by
  unfold czPositiveFamily0
  apply (List.nodup_range (r - 1)).map
  intro a b h
  have hc := congrArg Prod.snd h
  simp at hc
  omega

theorem czNegativeFamily0_nodup (s r : ℕ) : (czNegativeFamily0 s r).Nodup := by
  unfold czNegativeFamily0
  apply (List.nodup_range (s - 1)).map
  intro a b h
  have hc := congrArg Prod.fst h
  simp at hc
  omega

theorem czSideFiveCells_nodup (s r : ℕ) : (czSideFiveCells s r).Nodup := by
  rw [czSideFiveCells, List.nodup_append]
  refine ⟨czPositiveFamily0_nodup s r, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨czPositiveFamily1_nodup s r, czPositiveFamily2_nodup s r,
      czPositiveFamily1_disjoint_family2 s r⟩
  · rw [List.disjoint_append_right]
    constructor
    · rw [List.disjoint_left]
      intro cell hp h1
      exact (List.disjoint_left.mp (czRawForward0_disjoint_family1 s r))
        (by
          simp [czPositiveFamily0, czRawForward0] at hp ⊢
          obtain ⟨q, hq, rfl⟩ := hp
          exact ⟨q, by omega, rfl⟩) h1
    · rw [List.disjoint_left]
      intro cell hp h2
      exact (List.disjoint_left.mp (czRawForward0_disjoint_family2 s r))
        (by
          simp [czPositiveFamily0, czRawForward0] at hp ⊢
          obtain ⟨q, hq, rfl⟩ := hp
          exact ⟨q, by omega, rfl⟩) h2

theorem czSideFiveNegativeCells_nodup (s r : ℕ) :
    (czSideFiveNegativeCells s r).Nodup := by
  rw [czSideFiveNegativeCells, List.nodup_append]
  refine ⟨czNegativeFamily0_nodup s r, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨czNegativeFamily1_nodup s r, czNegativeFamily2_nodup s r,
      czNegativeFamily1_disjoint_family2 s r⟩
  · rw [List.disjoint_append_right]
    constructor
    · rw [List.disjoint_left]
      intro cell hn h1
      exact (List.disjoint_left.mp (czRawReverse0_disjoint_family1 s r))
        (by
          simp [czNegativeFamily0, czRawReverse0] at hn ⊢
          obtain ⟨q, hq, rfl⟩ := hn
          exact ⟨q + 1, by omega, by
            push_cast
            apply Prod.ext <;> ring⟩) h1
    · rw [List.disjoint_left]
      intro cell hn h2
      exact (List.disjoint_left.mp (czRawReverse0_disjoint_family2 s r))
        (by
          simp [czNegativeFamily0, czRawReverse0] at hn ⊢
          obtain ⟨q, hq, rfl⟩ := hn
          exact ⟨q + 1, by omega, by
            push_cast
            apply Prod.ext <;> ring⟩) h2

theorem czCPerimeterEdges_nodup (s r : ℕ) : (czCPerimeterEdges s r).Nodup := by
  rw [czCPerimeterEdges, List.nodup_append]
  refine ⟨(czSideFiveCells_nodup s r).map cellBoundaryEdgeAt_sideFive_injective,
    (czSideFiveNegativeCells_nodup s r).map
      reverse_cellBoundaryEdgeAt_sideFive_injective, ?_⟩
  rw [List.disjoint_left]
  intro edge hp hn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp
  obtain ⟨n, hn, heq⟩ := List.mem_map.mp hn
  have hneighbor := cellBoundaryEdgeAt_neighbor_exact n .side₅
  simp only [oppositeHexSide] at hneighbor
  have hedge : cellBoundaryEdgeAt (neighboringCell n .side₅) .side₂ =
      cellBoundaryEdgeAt p .side₅ := by rw [hneighbor, heq]
  have hsides := (cellBoundaryEdgeAt_eq_iff p
    (neighboringCell n .side₅) .side₅ .side₂).mp hedge |>.2
  cases hsides

theorem czCPerimeterEdges_label (s r : ℕ) {edge : LabeledHexEdge}
    (h : edge ∈ czCPerimeterEdges s r) : edge.label = .c := by
  simp only [czCPerimeterEdges, List.mem_append, List.mem_map] at h
  rcases h with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩ <;> rfl

theorem czBPerimeterEdges_label (s r : ℕ) {edge : LabeledHexEdge}
    (h : edge ∈ czBPerimeterEdges s r) : edge.label = .b := by
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp h
  change d4RotateLabel source.label = .b
  rw [czCPerimeterEdges_label s r hs]
  rfl

theorem czAPerimeterEdges_label (s r : ℕ) {edge : LabeledHexEdge}
    (h : edge ∈ czAPerimeterEdges s r) : edge.label = .a := by
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp h
  change d4RotateLabel source.label = .a
  rw [czBPerimeterEdges_label s r hs]
  rfl

theorem czPerimeterEdges_nodup (s r : ℕ) : (czPerimeterEdges s r).Nodup := by
  have hc := czCPerimeterEdges_nodup s r
  have hb : (czBPerimeterEdges s r).Nodup := hc.map d4RotateEdge_injective
  have ha : (czAPerimeterEdges s r).Nodup := hb.map d4RotateEdge_injective
  rw [czPerimeterEdges, List.nodup_append]
  constructor
  · rw [List.nodup_append]
    refine ⟨hc, hb, ?_⟩
    rw [List.disjoint_left]
    intro edge hec heb
    cases (czCPerimeterEdges_label s r hec).symm.trans
      (czBPerimeterEdges_label s r heb)
  · refine ⟨ha, ?_⟩
    rw [List.disjoint_left]
    intro edge hcb hea
    rw [List.mem_append] at hcb
    rcases hcb with hc' | hb'
    · cases (czCPerimeterEdges_label s r hc').symm.trans
        (czAPerimeterEdges_label s r hea)
    · cases (czBPerimeterEdges_label s r hb').symm.trans
        (czAPerimeterEdges_label s r hea)

theorem czSideFiveCells_length
    (s r : ℕ) (hr : 1 ≤ r) :
    (czSideFiveCells s r).length = 2 * (s + r) - 1 := by
  simp [czSideFiveCells, czPositiveFamily0, czPositiveFamily1,
    czPositiveFamily2, List.length_flatMap, Function.comp_def]
  omega

theorem czSideFiveNegativeCells_length
    (s r : ℕ) (hs : 1 ≤ s) :
    (czSideFiveNegativeCells s r).length = 2 * (s + r) - 1 := by
  simp [czSideFiveNegativeCells, czNegativeFamily0, czNegativeFamily1,
    czNegativeFamily2, List.length_flatMap, Function.comp_def]
  omega

theorem czPerimeterEdges_length
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (czPerimeterEdges s r).length = 12 * (s + r) - 6 := by
  simp [czPerimeterEdges, czBPerimeterEdges, czAPerimeterEdges,
    czCPerimeterEdges, czSideFiveCells_length s r hr,
    czSideFiveNegativeCells_length s r hs]
  omega

theorem czReducedCoefficient_positiveSideFive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) {cell : Cell}
    (hcell : cell ∈ czSideFiveCells s r) :
    directedEdgeCoefficient (czReducedBoundaryWalk s r)
      (cellBoundaryEdgeAt cell .side₅) = 1 := by
  rw [directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr,
    offsetCellBoundaryCoefficient]
  have hg := (mem_czSideFiveCells_iff s r hs hr cell).1 hcell
  have hp := classZeroOffsetParameters s r hs hr
  rw [hp.1, hp.2]
  simp [hg.1, hg.2]

theorem czReducedCoefficient_negativeSideFive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) {cell : Cell}
    (hcell : cell ∈ czSideFiveNegativeCells s r) :
    directedEdgeCoefficient (czReducedBoundaryWalk s r)
      (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) = 1 := by
  rw [directedEdgeCoefficient_reverse_target,
    directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr,
    offsetCellBoundaryCoefficient]
  have hg := (mem_czSideFiveNegativeCells_iff s r hs hr cell).1 hcell
  have hp := classZeroOffsetParameters s r hs hr
  rw [hp.1, hp.2]
  simp [hg.1, hg.2]

theorem czReducedCoefficient_rotateSideFive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    directedEdgeCoefficient (czReducedBoundaryWalk s r)
        (d4RotateEdge (cellBoundaryEdgeAt cell .side₅)) =
      directedEdgeCoefficient (czReducedBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [d4RotateEdge_cell_sideFive,
    directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr,
    directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr,
    czCellBoundaryCoefficient_rotate_sideFive]

theorem czReducedCoefficient_rotateTwiceSideFive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    directedEdgeCoefficient (czReducedBoundaryWalk s r)
        (d4RotateEdge (d4RotateEdge (cellBoundaryEdgeAt cell .side₅))) =
      directedEdgeCoefficient (czReducedBoundaryWalk s r)
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [d4RotateEdge_cell_sideFive, d4RotateEdge_cell_sideThree,
    directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr,
    directedEdgeCoefficient_czReducedBoundary_allSides s r hs hr,
    czCellBoundaryCoefficient_rotate_sideThree,
    czCellBoundaryCoefficient_rotate_sideFive]

theorem czPerimeterEdge_coefficient_one
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) {edge : LabeledHexEdge}
    (hedge : edge ∈ czPerimeterEdges s r) :
    directedEdgeCoefficient (czReducedBoundaryWalk s r) edge = 1 := by
  rw [czPerimeterEdges, List.mem_append, List.mem_append] at hedge
  rcases hedge with (hc | hb) | ha
  · simp only [czCPerimeterEdges, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · exact czReducedCoefficient_positiveSideFive s r hs hr hcell
    · exact czReducedCoefficient_negativeSideFive s r hs hr hcell
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hb
    simp only [czCPerimeterEdges, List.mem_append, List.mem_map] at hsource
    rcases hsource with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · rw [czReducedCoefficient_rotateSideFive s r hs hr]
      exact czReducedCoefficient_positiveSideFive s r hs hr hcell
    · rw [d4RotateEdge_reverse, directedEdgeCoefficient_reverse_target,
        czReducedCoefficient_rotateSideFive s r hs hr]
      have hneg := czReducedCoefficient_negativeSideFive s r hs hr hcell
      rw [directedEdgeCoefficient_reverse_target] at hneg
      omega
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp ha
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hsource
    simp only [czCPerimeterEdges, List.mem_append, List.mem_map] at horiginal
    rcases horiginal with ⟨cell, hcell, rfl⟩ | ⟨cell, hcell, rfl⟩
    · rw [czReducedCoefficient_rotateTwiceSideFive s r hs hr]
      exact czReducedCoefficient_positiveSideFive s r hs hr hcell
    · rw [d4RotateEdge_reverse, d4RotateEdge_reverse,
        directedEdgeCoefficient_reverse_target,
        czReducedCoefficient_rotateTwiceSideFive s r hs hr]
      have hneg := czReducedCoefficient_negativeSideFive s r hs hr hcell
      rw [directedEdgeCoefficient_reverse_target] at hneg
      omega

theorem czPerimeterEdges_subset_reduced
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    ∀ edge ∈ czPerimeterEdges s r, edge ∈ czReducedBoundaryWalk s r := by
  intro edge hedge
  exact edge_mem_of_directedEdgeCoefficient_eq_one _ _
    (czPerimeterEdge_coefficient_one s r hs hr hedge)

theorem czReducedBoundary_length_lower
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    12 * (s + r) - 6 ≤ (czReducedBoundaryWalk s r).length := by
  rw [← czPerimeterEdges_length s r hs hr,
    ← List.toFinset_card_of_nodup (czPerimeterEdges_nodup s r),
    ← List.toFinset_card_of_nodup (czReducedBoundary_nodup s r)]
  apply Finset.card_le_card
  intro edge hedge
  exact List.mem_toFinset.mpr
    (czPerimeterEdges_subset_reduced s r hs hr edge
      (List.mem_toFinset.mp hedge))

end FiniteDefects
