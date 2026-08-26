import D4KernelOnly.D4BoundaryReverseSideFiveOccurrences

/-! # The exact side-five directed coefficient identity -/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4SpurCell (m : ℕ) : Cell := (1, -((m : ℤ)) - 2)

theorem mem_d4WalkForwardSideFiveCells_iff (m : ℕ) (cell : Cell) :
    cell ∈ d4WalkForwardSideFiveCells m ↔
      cell = d4SpurCell m ∨ cell ∈ d4SideFiveCells m := by
  simp [d4WalkForwardSideFiveCells, d4SideFiveCells, d4SpurCell]

theorem mem_d4WalkReverseSideFiveCells_iff (m : ℕ) (cell : Cell) :
    cell ∈ d4WalkReverseSideFiveCells m ↔
      cell = d4SpurCell m ∨ cell ∈ d4SideFiveNegativeCells m := by
  simp [d4WalkReverseSideFiveCells, d4SideFiveNegativeCells,
    d4SpurCell]
  aesop

theorem d4Spur_not_positive (m : ℕ) :
    d4SpurCell m ∉ d4SideFiveCells m := by
  rw [mem_d4SideFiveCells_iff]
  simp [d4SpurCell, inBenzel, neighboringCell]
  omega

theorem d4Spur_not_negative (m : ℕ) :
    d4SpurCell m ∉ d4SideFiveNegativeCells m := by
  rw [mem_d4SideFiveNegativeCells_iff]
  simp [d4SpurCell, inBenzel, neighboringCell]
  omega

theorem d4SideFiveCells_nodup (m : ℕ) :
    (d4SideFiveCells m).Nodup := by
  simp [d4SideFiveCells, List.nodup_append, List.pairwise_append,
    List.disjoint_left, Function.onFun]
  aesop (config := { warnOnNonterminal := false })
  all_goals try omega
  all_goals
    rw [← List.map_eq_flatMap]
    rw [List.map_map]
    apply (List.nodup_range (m + 1)).map
    intro r s hrs
    have hfst := congrArg Prod.fst hrs
    have hsnd := congrArg Prod.snd hrs
    simp only [Function.comp_apply] at hfst hsnd
    omega

theorem d4SideFiveNegativeCells_nodup (m : ℕ) :
    (d4SideFiveNegativeCells m).Nodup := by
  simp [d4SideFiveNegativeCells, List.nodup_append,
    List.nodup_flatMap, List.pairwise_append,
    List.disjoint_left, Function.onFun]
  aesop (config := { warnOnNonterminal := false })
  all_goals try omega
  apply (List.pairwise_lt_range (m + 1)).imp
  intro r s hrs
  simp [Function.onFun, List.disjoint_left]
  omega

theorem d4WalkForwardSideFiveCells_nodup (m : ℕ) :
    (d4WalkForwardSideFiveCells m).Nodup := by
  have htail := d4SideFiveCells_nodup m
  have hspur := d4Spur_not_positive m
  simpa [d4WalkForwardSideFiveCells, d4SideFiveCells, d4SpurCell,
    List.nodup_append] using List.nodup_cons.mpr ⟨hspur, htail⟩

theorem d4WalkReverseSideFiveCells_nodup (m : ℕ) :
    (d4WalkReverseSideFiveCells m).Nodup := by
  let prefixCells : List Cell :=
    (List.range (m + 1)).flatMap fun r =>
      [(-((m : ℤ)) - 2 + (r : ℤ),
          (m : ℤ) + 1 - 2 * (r : ℤ)),
        (-((m : ℤ)) - 2 + (r : ℤ),
          (m : ℤ) - 2 * (r : ℤ))]
  let endpoint : Cell := (-1, -((m : ℤ)) - 1)
  let spur := d4SpurCell m
  let last : Cell := (-((m : ℤ)) - 2, (m : ℤ) + 2)
  have hperm : List.Perm (d4WalkReverseSideFiveCells m)
      (spur :: d4SideFiveNegativeCells m) := by
    have hcomm : List.Perm
        (prefixCells ++ [endpoint, spur, last])
        ([endpoint, spur, last] ++ prefixCells) :=
      List.perm_append_comm
    have hswap : List.Perm
        ([endpoint, spur, last] ++ prefixCells)
        (spur :: [endpoint, last] ++ prefixCells) := by
      simpa using (List.Perm.swap endpoint spur (last :: prefixCells)).symm
    have htail : List.Perm
        (spur :: [endpoint, last] ++ prefixCells)
        (spur :: prefixCells ++ [endpoint, last]) :=
      List.Perm.cons spur List.perm_append_comm
    simpa [prefixCells, endpoint, spur, last,
      d4WalkReverseSideFiveCells, d4SideFiveNegativeCells] using
      hcomm.trans (hswap.trans htail)
  apply hperm.nodup_iff.mpr
  exact List.nodup_cons.mpr
    ⟨d4Spur_not_negative m, d4SideFiveNegativeCells_nodup m⟩

theorem count_filter_eq_count_of_true
    {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha]
    (items : List Alpha) (predicate : Alpha → Bool) (item : Alpha)
    (hitem : predicate item = true) :
    (items.filter predicate).count item = items.count item := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      cases hhead : predicate head with
      | false =>
          have hne : head ≠ item := by
            intro heq
            subst head
            simp [hitem] at hhead
          simp only [List.filter_cons, hhead, Bool.false_eq_true,
            if_false]
          rw [ih, List.count_cons]
          simp [hne, Ne.symm hne]
      | true =>
          simp only [List.filter_cons, hhead, if_true]
          rw [List.count_cons, List.count_cons, ih]

theorem lawful_count_map_of_injective
    {Alpha Beta : Type*}
    [BEq Alpha] [LawfulBEq Alpha] [BEq Beta] [LawfulBEq Beta]
    (items : List Alpha) (mapItem : Alpha → Beta)
    (hinjective : Function.Injective mapItem) (item : Alpha) :
    (items.map mapItem).count (mapItem item) = items.count item := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      rw [List.map_cons, List.count_cons, List.count_cons, ih]
      by_cases heq : head = item
      · subst head
        simp
      · have hmapped : mapItem head ≠ mapItem item := by
          intro h
          exact heq (hinjective h)
        simp [heq, Ne.symm heq, hmapped, Ne.symm hmapped]

theorem isForwardSideFiveEdge_cellBoundaryEdgeAt
    (cell : Cell) :
    isForwardSideFiveEdge (cellBoundaryEdgeAt cell .side₅) = true := by
  rw [cellBoundaryEdgeAt_sideFive_formula]
  simp [isForwardSideFiveEdge, advanceLabeledHexEdge]

theorem isReverseSideFiveEdge_reverse_cellBoundaryEdgeAt
    (cell : Cell) :
    isReverseSideFiveEdge
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) = true := by
  rw [reverse_cellBoundaryEdgeAt_sideFive_formula]
  simp [isReverseSideFiveEdge, advanceLabeledHexEdge]

theorem cellBoundaryEdgeAt_sideFive_injective :
    Function.Injective (fun cell : Cell =>
      cellBoundaryEdgeAt cell .side₅) := by
  intro left right hedge
  exact (cellBoundaryEdgeAt_eq_iff right left .side₅ .side₅).mp hedge |>.1

theorem reverse_cellBoundaryEdgeAt_sideFive_injective :
    Function.Injective (fun cell : Cell =>
      reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) := by
  intro left right hedge
  apply cellBoundaryEdgeAt_sideFive_injective
  exact reverseLabeledHexEdge_injective hedge

theorem d4LiteralBoundaryWalk_forward_count
    (m : ℕ) (cell : Cell) :
    (d4LiteralBoundaryWalk m).count (cellBoundaryEdgeAt cell .side₅) =
      (d4WalkForwardSideFiveCells m).count cell := by
  have hfilter := count_filter_eq_count_of_true
    (d4LiteralBoundaryWalk m) isForwardSideFiveEdge
      (cellBoundaryEdgeAt cell .side₅)
      (isForwardSideFiveEdge_cellBoundaryEdgeAt cell)
  rw [← forwardSideFiveEdges] at hfilter
  rw [d4LiteralBoundaryWalk_forward, d4WalkForwardSideFiveEdges,
    lawful_count_map_of_injective _ _
      cellBoundaryEdgeAt_sideFive_injective] at hfilter
  exact hfilter.symm

theorem d4LiteralBoundaryWalk_reverse_count
    (m : ℕ) (cell : Cell) :
    (d4LiteralBoundaryWalk m).count
        (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅)) =
      (d4WalkReverseSideFiveCells m).count cell := by
  have hfilter := count_filter_eq_count_of_true
    (d4LiteralBoundaryWalk m) isReverseSideFiveEdge
      (reverseLabeledHexEdge (cellBoundaryEdgeAt cell .side₅))
      (isReverseSideFiveEdge_reverse_cellBoundaryEdgeAt cell)
  rw [← reverseSideFiveEdges] at hfilter
  rw [d4LiteralBoundaryWalk_reverse, d4WalkReverseSideFiveEdges,
    lawful_count_map_of_injective _ _
      reverse_cellBoundaryEdgeAt_sideFive_injective] at hfilter
  exact hfilter.symm

theorem d4WalkSideFiveCell_count_difference
    (m : ℕ) (cell : Cell) :
    ((d4WalkForwardSideFiveCells m).count cell : ℤ) -
        (d4WalkReverseSideFiveCells m).count cell =
      (if cell ∈ d4SideFiveCells m then (1 : ℤ) else 0) -
        (if cell ∈ d4SideFiveNegativeCells m then (1 : ℤ) else 0) := by
  rw [lawful_count_eq_indicator_of_nodup _
      (d4WalkForwardSideFiveCells_nodup m),
    lawful_count_eq_indicator_of_nodup _
      (d4WalkReverseSideFiveCells_nodup m)]
  simp only [mem_d4WalkForwardSideFiveCells_iff,
    mem_d4WalkReverseSideFiveCells_iff]
  by_cases hspur : cell = d4SpurCell m
  · subst cell
    simp [d4Spur_not_positive, d4Spur_not_negative]
  · simp [hspur]

theorem directedEdgeCoefficient_d4LiteralBoundaryWalk_sideFive
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient (d4LiteralBoundaryWalk m)
        (cellBoundaryEdgeAt cell .side₅) =
      directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₅) := by
  rw [directedEdgeCoefficient,
    d4LiteralBoundaryWalk_forward_count,
    d4LiteralBoundaryWalk_reverse_count,
    d4WalkSideFiveCell_count_difference,
    directedEdgeCoefficient_d4CellBoundaries_sideFive]

end FiniteDefects
