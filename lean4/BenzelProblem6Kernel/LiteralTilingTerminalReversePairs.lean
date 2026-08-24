import BenzelProblem6Kernel.LiteralTilingTerminalEdgeAccounting

/-! # Reverse-pair closure inherited by the terminal contour -/

namespace BenzelProblem6Kernel

theorem selectedEdgePair_reverse_mem
    (edge selected : LabeledHexEdge)
    (hmem : edge ∈ selectedEdgePair selected) :
    reverseLabeledHexEdge edge ∈ selectedEdgePair selected := by
  simp only [selectedEdgePair, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with hedge | hedge
  · subst edge
    simp [selectedEdgePair, reverseLabeledHexEdge_involutive]
  · subst edge
    simp [selectedEdgePair, reverseLabeledHexEdge_involutive]

theorem RightmostPeelingSkeleton.selectedEdgePairs_reverse_mem {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements)
    {edge : LabeledHexEdge} (hedge : edge ∈ skeleton.selectedEdgePairs) :
    reverseLabeledHexEdge edge ∈ skeleton.selectedEdgePairs := by
  induction skeleton with
  | done => simp [RightmostPeelingSkeleton.selectedEdgePairs] at hedge
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      simp only [RightmostPeelingSkeleton.selectedEdgePairs,
        List.mem_append] at hedge ⊢
      rcases hedge with hedgeRest | hedgePair
      · exact Or.inl (ih hedgeRest)
      · exact Or.inr (selectedEdgePair_reverse_mem
          edge splice.sharedEdge hedgePair)

theorem literalTilingRightmostTerminal_reverse_mem {m : ℕ}
    (tiling : LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ (literalTilingRightmostTerminal tiling).edges) :
    reverseLabeledHexEdge edge ∈
      (literalTilingRightmostTerminal tiling).edges := by
  let skeleton := literalTilingRightmostSkeleton tiling
  have haccount := literalTilingTerminal_edgeAccounting_perm tiling
  have hedgeComplex : edge ∈ literalTilingComplexDirectedEdges tiling :=
    haccount.mem_iff.mpr (List.mem_append_left _ hedge)
  have hreverseComplex : reverseLabeledHexEdge edge ∈
      literalTilingComplexDirectedEdges tiling :=
    literalTilingComplexDirectedEdges_reverse_mem tiling hedgeComplex
  have hreverseSplit : reverseLabeledHexEdge edge ∈
      (literalTilingRightmostTerminal tiling).edges ++
        skeleton.selectedEdgePairs :=
    haccount.mem_iff.mp hreverseComplex
  rw [List.mem_append] at hreverseSplit
  rcases hreverseSplit with hterminal | hselected
  · exact hterminal
  · have hedgeSelected : edge ∈ skeleton.selectedEdgePairs := by
      simpa [reverseLabeledHexEdge_involutive] using
        skeleton.selectedEdgePairs_reverse_mem hselected
    exact (List.disjoint_left.mp
      (literalTilingRightmostTerminal_disjoint_selected tiling))
        hedge hedgeSelected |>.elim

end BenzelProblem6Kernel
