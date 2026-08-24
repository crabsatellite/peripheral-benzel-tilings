import BenzelProblem6Kernel.IncidenceComponents

/-!
# Counting component cells by their unique tiling placements
-/

namespace BenzelProblem6Kernel

theorem cell_mem_component_iff_coveringPlacement {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent)
    (cell : BenzelCell (m + 5)) :
    cell ∈ componentCells tiling component ↔
      coveringPlacementNode tiling cell ∈ componentPlacements tiling component := by
  classical
  simp only [componentCells, componentPlacements, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hcell
    rw [← cell_component_eq_tile_component tiling cell]
    exact hcell
  · intro hplacement
    rw [cell_component_eq_tile_component tiling cell]
    exact hplacement

theorem component_cell_fiber_eq_placementCells {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent)
    (placement : TilingPlacementNode tiling)
    (hplacement : placement ∈ componentPlacements tiling component) :
    (componentCells tiling component).filter
        (fun cell => coveringPlacementNode tiling cell = placement) =
      placementBenzelCells placement.1 := by
  classical
  ext cell
  simp only [Finset.mem_filter, mem_placementBenzelCells_iff]
  constructor
  · rintro ⟨_, hcovering⟩
    rw [← hcovering]
    exact coveringPlacementNode_covers tiling cell
  · intro hcover
    have hcovering := coveringPlacementNode_eq_of_covers tiling cell placement hcover
    refine ⟨?_, hcovering⟩
    apply (cell_mem_component_iff_coveringPlacement tiling component cell).2
    rw [hcovering]
    exact hplacement

theorem componentCells_card_eq_three_mul_placements {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    (componentCells tiling component).card =
      3 * (componentPlacements tiling component).card := by
  classical
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := componentCells tiling component)
    (t := componentPlacements tiling component)
    (f := coveringPlacementNode tiling)
    (fun cell hcell =>
      (cell_mem_component_iff_coveringPlacement tiling component cell).1 hcell)
  rw [hfiber]
  calc
    (∑ placement ∈ componentPlacements tiling component,
        ((componentCells tiling component).filter
          (fun cell => coveringPlacementNode tiling cell = placement)).card) =
        ∑ _placement ∈ componentPlacements tiling component, 3 := by
      apply Finset.sum_congr rfl
      intro placement hplacement
      rw [component_cell_fiber_eq_placementCells tiling component placement
        hplacement, card_placementBenzelCells]
    _ = 3 * (componentPlacements tiling component).card := by
      simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

end BenzelProblem6Kernel
