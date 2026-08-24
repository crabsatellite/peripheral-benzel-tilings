import BenzelProblem6Kernel.GeometricSpliceExistence

/-!
# The deterministic rightmost peeling skeleton

The construction removes every placement and records every exact geometric
splice.  It is premise-free once supplied a rooted current boundary and the
side-five coefficient invariant.  The terminal tree and word theorems are
proved in the downstream closure modules.
-/

namespace BenzelProblem6Kernel

inductive RightmostPeelingSkeleton (m : ℕ) :
    RootedAlternatingBoundary → Finset (LiteralPlacement m) → Type
  | done (region : RootedAlternatingBoundary) :
      RightmostPeelingSkeleton m region ∅
  | peel (region : RootedAlternatingBoundary)
      (placements : Finset (LiteralPlacement m))
      (splice : GeometricTileBoundarySplice m)
      (boundary_exact : splice.boundary = region.edges)
      (placement_mem : splice.placement ∈ placements)
      (selectedCell : Cell)
      (selectedCell_mem : selectedCell ∈ splice.placement.cells)
      (sharedEdge_exact : splice.sharedEdge =
        cellBoundaryEdgeAt selectedCell .side₅)
      (neighbor_outside : neighboringCell selectedCell .side₅ ∉
        placementUnionCells placements)
      (selectedCell_not_remaining : selectedCell ∉
        placementUnionCells (placements.erase splice.placement))
      (rest : RightmostPeelingSkeleton m
        (region.spliceRemaining splice boundary_exact)
        (placements.erase splice.placement)) :
      RightmostPeelingSkeleton m region placements

noncomputable def buildRightmostPeelingSkeleton {m : ℕ}
    (tiling : LiteralTiling m)
    (region : RootedAlternatingBoundary)
    (placements : Finset (LiteralPlacement m))
    (hsubset : placements ⊆ tiling.1)
    (hinvariant : RightmostBoundaryCoefficientInvariant
      region.edges placements) :
    RightmostPeelingSkeleton m region placements := by
  classical
  by_cases hempty : placements = ∅
  · subst placements
    exact .done region
  · have hnonempty : placements.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let candidate := Classical.choice
      (currentRightmostExposedEdge_nonempty tiling placements
        hsubset hnonempty region.edges hinvariant)
    let edge := cellBoundaryEdgeAt candidate.cell .side₅
    let available := Classical.choice
      (availableGeometricTileSplice_nonempty region candidate.placement edge
        candidate.boundary_edge_mem candidate.placement_edge_mem)
    let splice := available.splice
    have hboundary : splice.boundary = region.edges := available.boundary_exact
    have hsplicePlacement : splice.placement = candidate.placement :=
      available.placement_exact
    have hplacement' : splice.placement ∈ placements := by
      rw [hsplicePlacement]
      exact candidate.placement_mem
    have hcell' : candidate.cell ∈ splice.placement.cells := by
      rw [hsplicePlacement]
      exact candidate.cell_mem
    have hcellNotRemaining : candidate.cell ∉
        placementUnionCells (placements.erase splice.placement) := by
      intro hremaining
      rw [placementUnionCells, Finset.mem_biUnion] at hremaining
      obtain ⟨other, hother, hotherCell⟩ := hremaining
      have hotherMem : other ∈ placements := Finset.mem_of_mem_erase hother
      let regionCell : BenzelCell (m + 5) :=
        ⟨candidate.cell,
          candidate.placement.2 candidate.cell candidate.cell_mem⟩
      obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
      have hcandidateEq : candidate.placement = covering :=
        hunique candidate.placement
          ⟨hsubset candidate.placement_mem, candidate.cell_mem⟩
      have hotherEq : other = covering :=
        hunique other ⟨hsubset hotherMem,
          List.mem_toFinset.mp hotherCell⟩
      have hsame : other = splice.placement :=
        (hotherEq.trans hcandidateEq.symm).trans hsplicePlacement.symm
      exact (Finset.mem_erase.mp hother).1 hsame
    have hsubset' : placements.erase splice.placement ⊆ tiling.1 := by
      intro candidate hcandidate
      exact hsubset (Finset.mem_of_mem_erase hcandidate)
    have hinvariant' : RightmostBoundaryCoefficientInvariant
        (region.spliceRemaining splice hboundary).edges
        (placements.erase splice.placement) := by
      change RightmostBoundaryCoefficientInvariant splice.remainingBoundary _
      exact rightmostBoundaryInvariant_after_raw_splice
        hinvariant splice hboundary hplacement'
    exact .peel region placements splice hboundary hplacement'
      candidate.cell hcell' available.edge_exact candidate.neighbor_outside
      hcellNotRemaining
      (buildRightmostPeelingSkeleton tiling
        (region.spliceRemaining splice hboundary)
        (placements.erase splice.placement) hsubset' hinvariant')
termination_by placements.card
decreasing_by
  exact Finset.card_erase_lt_of_mem hplacement'

def RightmostPeelingSkeleton.removedPlacements {m : ℕ} :
    {region : RootedAlternatingBoundary} →
    {placements : Finset (LiteralPlacement m)} →
      RightmostPeelingSkeleton m region placements →
        List (LiteralPlacement m)
  | _, _, .done _ => []
  | _, _, .peel _ _ splice _ _ _ _ _ _ _ rest =>
      splice.placement :: rest.removedPlacements

def RightmostPeelingSkeleton.terminalRegion {m : ℕ} :
    {region : RootedAlternatingBoundary} →
    {placements : Finset (LiteralPlacement m)} →
      RightmostPeelingSkeleton m region placements →
        RootedAlternatingBoundary
  | _, _, .done region => region
  | _, _, .peel _ _ _ _ _ _ _ _ _ _ rest => rest.terminalRegion

theorem RightmostPeelingSkeleton.removedPlacements_perm {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    List.Perm skeleton.removedPlacements placements.toList := by
  induction skeleton with
  | done => simp [RightmostPeelingSkeleton.removedPlacements]
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      have hcons : List.Perm
          (splice.placement :: rest.removedPlacements)
          (splice.placement :: (placements.erase splice.placement).toList) :=
        List.Perm.cons splice.placement ih
      exact hcons.trans
        (finset_toList_perm_cons_erase placements placement_mem).symm

noncomputable def RightmostPeelingSkeleton.toGeometricPeeling {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements)
    (terminal_empty : InvolutiveWordEquivalent
      (labeledEdgeWord skeleton.terminalRegion.edges) []) :
    GeometricBoundaryPeeling m region.edges := by
  induction skeleton with
  | done terminal =>
      exact .done terminal.edges terminal_empty
  | peel current currentPlacements splice boundary_exact
      placement_mem selectedCell selectedCell_mem sharedEdge_exact
      neighbor_outside selectedCell_not_remaining rest ih =>
      exact .peel current.edges splice boundary_exact
        splice.remainingBoundary (Relation.EqvGen.refl _) (ih terminal_empty)

theorem RightmostPeelingSkeleton.toGeometricPeeling_placements {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements)
    (terminal_empty : InvolutiveWordEquivalent
      (labeledEdgeWord skeleton.terminalRegion.edges) []) :
    (skeleton.toGeometricPeeling terminal_empty).placements =
      skeleton.removedPlacements := by
  induction skeleton with
  | done => rfl
  | peel current currentPlacements splice boundary_exact
      placement_mem selectedCell selectedCell_mem sharedEdge_exact
      neighbor_outside selectedCell_not_remaining rest ih =>
      simp only [RightmostPeelingSkeleton.toGeometricPeeling,
        GeometricBoundaryPeeling.placements,
        RightmostPeelingSkeleton.removedPlacements]
      exact congrArg (List.cons splice.placement) (ih terminal_empty)

end BenzelProblem6Kernel
