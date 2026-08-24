import BenzelProblem6Kernel.HexCellAdjacency
import BenzelProblem6Kernel.RightmostPeelingSkeleton

/-!
# Literal traces of the rightmost peeling recursion

Each peel records one distinct covered cell and its positive-first-coordinate
edge.  The cell witness is retained independently of the noncomputable choice
used to select the peel.
-/

namespace BenzelProblem6Kernel

def RightmostPeelingSkeleton.selectedCells {m : ℕ} :
    {region : RootedAlternatingBoundary} →
    {placements : Finset (LiteralPlacement m)} →
      RightmostPeelingSkeleton m region placements → List Cell
  | _, _, .done _ => []
  | _, _, .peel _ _ _ _ _ selectedCell _ _ _ _ rest =>
      selectedCell :: rest.selectedCells

def RightmostPeelingSkeleton.selectedEdges {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    List LabeledHexEdge :=
  skeleton.selectedCells.map
    (fun cell => cellBoundaryEdgeAt cell .side₅)

theorem side₅BoundaryEdge_injective :
    Function.Injective (fun cell : Cell =>
      cellBoundaryEdgeAt cell .side₅) := by
  intro left right hedge
  exact (cellBoundaryEdgeAt_eq_iff right left .side₅ .side₅).mp hedge |>.1

theorem RightmostPeelingSkeleton.selectedCells_mem_union {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    ∀ cell ∈ skeleton.selectedCells,
      cell ∈ placementUnionCells placements := by
  induction skeleton with
  | done => simp [RightmostPeelingSkeleton.selectedCells]
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      intro cell hcell
      simp only [RightmostPeelingSkeleton.selectedCells,
        List.mem_cons] at hcell
      rcases hcell with rfl | hrest
      · rw [placementUnionCells, Finset.mem_biUnion]
        exact ⟨splice.placement, placement_mem,
          List.mem_toFinset.mpr selectedCell_mem⟩
      · have hremaining := ih cell hrest
        rw [placementUnionCells, Finset.mem_biUnion] at hremaining ⊢
        obtain ⟨placement, hplacement, hplacementCell⟩ := hremaining
        exact ⟨placement, Finset.mem_of_mem_erase hplacement,
          hplacementCell⟩

theorem RightmostPeelingSkeleton.selectedCells_nodup {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    skeleton.selectedCells.Nodup := by
  induction skeleton with
  | done => simp [RightmostPeelingSkeleton.selectedCells]
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      rw [RightmostPeelingSkeleton.selectedCells, List.nodup_cons]
      constructor
      · intro hselected
        exact selectedCell_not_remaining
          (rest.selectedCells_mem_union selectedCell hselected)
      · exact ih

theorem RightmostPeelingSkeleton.selectedEdges_nodup {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    skeleton.selectedEdges.Nodup := by
  exact skeleton.selectedCells_nodup.map side₅BoundaryEdge_injective

theorem RightmostPeelingSkeleton.selectedCells_length {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    skeleton.selectedCells.length = skeleton.removedPlacements.length := by
  induction skeleton with
  | done => rfl
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      simp only [RightmostPeelingSkeleton.selectedCells,
        RightmostPeelingSkeleton.removedPlacements, List.length_cons]
      exact congrArg Nat.succ ih

theorem RightmostPeelingSkeleton.selectedEdges_length {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    skeleton.selectedEdges.length = skeleton.removedPlacements.length := by
  rw [RightmostPeelingSkeleton.selectedEdges, List.length_map,
    skeleton.selectedCells_length]

end BenzelProblem6Kernel
