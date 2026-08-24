import BenzelProblem6Kernel.LiteralPlacementBoundaryNodup

/-! # Duplicate-free directed boundary edges across a literal tiling -/

namespace BenzelProblem6Kernel

theorem literalPlacementBoundary_edge_has_cell {m : ℕ}
    (placement : LiteralPlacement m) {edge : LabeledHexEdge}
    (hedge : edge ∈ literalPlacementBoundary placement) :
    ∃ cell ∈ placement.cells, edge ∈ labeledCellBoundary cell := by
  have hsubset := literalPrototypeBoundary_subset_cellBoundaries
    placement.tile placement.base hedge
  change edge ∈ orientedCellBoundaryList placement.cells at hsubset
  rw [orientedCellBoundaryList, List.mem_flatMap] at hsubset
  exact hsubset

theorem common_directed_cellBoundary_edge_forces_cell_eq
    {left right : Cell} {edge : LabeledHexEdge}
    (hleft : edge ∈ labeledCellBoundary left)
    (hright : edge ∈ labeledCellBoundary right) :
    left = right := by
  rw [labeledCellBoundary_eq_allEdges] at hleft
  simp only [allCellBoundaryEdges, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hleft
  rcases hleft with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ((edge_mem_labeledCellBoundary_iff left right .side₀).mp hright).symm
  · exact ((edge_mem_labeledCellBoundary_iff left right .side₁).mp hright).symm
  · exact ((edge_mem_labeledCellBoundary_iff left right .side₂).mp hright).symm
  · exact ((edge_mem_labeledCellBoundary_iff left right .side₃).mp hright).symm
  · exact ((edge_mem_labeledCellBoundary_iff left right .side₄).mp hright).symm
  · exact ((edge_mem_labeledCellBoundary_iff left right .side₅).mp hright).symm

theorem literalPlacementBoundaries_disjoint_in_tiling {m : ℕ}
    (tiling : LiteralTiling m)
    {left right : LiteralPlacement m}
    (hleft : left ∈ tiling.1) (hright : right ∈ tiling.1)
    (hne : left ≠ right) :
    List.Disjoint (literalPlacementBoundary left)
      (literalPlacementBoundary right) := by
  rw [List.disjoint_left]
  intro edge hedgeLeft hedgeRight
  obtain ⟨leftCell, hleftCell, hleftEdge⟩ :=
    literalPlacementBoundary_edge_has_cell left hedgeLeft
  obtain ⟨rightCell, hrightCell, hrightEdge⟩ :=
    literalPlacementBoundary_edge_has_cell right hedgeRight
  have hcell : leftCell = rightCell :=
    common_directed_cellBoundary_edge_forces_cell_eq hleftEdge hrightEdge
  subst rightCell
  let regionCell : BenzelCell (m + 5) :=
    ⟨leftCell, left.2 leftCell hleftCell⟩
  obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
  have hleftEq : left = covering :=
    hunique left ⟨hleft, hleftCell⟩
  have hrightEq : right = covering :=
    hunique right ⟨hright, hrightCell⟩
  exact hne (hleftEq.trans hrightEq.symm)

theorem literalPlacementBoundaryList_nodup {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalPlacementBoundaryList tiling.1.toList).Nodup := by
  rw [literalPlacementBoundaryList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact literalPlacementBoundary_nodup placement
  · apply (Finset.nodup_toList tiling.1).pairwise_of_forall_ne
    intro left hleft right hright hne
    exact literalPlacementBoundaries_disjoint_in_tiling tiling
      (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne

def reverseLiteralPlacementBoundaryList {m : ℕ}
    (placements : List (LiteralPlacement m)) :
    List LabeledHexEdge :=
  placements.flatMap (fun placement =>
    reverseReorientedEdges (literalPlacementBoundary placement))

theorem reverseReorientedEdges_disjoint
    {left right : List LabeledHexEdge}
    (hdisjoint : List.Disjoint left right) :
    List.Disjoint (reverseReorientedEdges left)
      (reverseReorientedEdges right) := by
  rw [List.disjoint_left]
  intro edge hedgeLeft hedgeRight
  simp only [reverseReorientedEdges, List.mem_map,
    List.mem_reverse] at hedgeLeft hedgeRight
  obtain ⟨leftEdge, hleftEdge, rfl⟩ := hedgeLeft
  obtain ⟨rightEdge, hrightEdge, hedge⟩ := hedgeRight
  have heq : leftEdge = rightEdge :=
    reverseLabeledHexEdge_injective hedge.symm
  subst rightEdge
  exact (List.disjoint_left.mp hdisjoint) hleftEdge hrightEdge

theorem reverseLiteralPlacementBoundaryList_nodup {m : ℕ}
    (tiling : LiteralTiling m) :
    (reverseLiteralPlacementBoundaryList tiling.1.toList).Nodup := by
  rw [reverseLiteralPlacementBoundaryList, List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact reverseLiteralPlacementBoundary_nodup placement
  · apply (Finset.nodup_toList tiling.1).pairwise_of_forall_ne
    intro left hleft right hright hne
    apply reverseReorientedEdges_disjoint
    exact literalPlacementBoundaries_disjoint_in_tiling tiling
      (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne

end BenzelProblem6Kernel
