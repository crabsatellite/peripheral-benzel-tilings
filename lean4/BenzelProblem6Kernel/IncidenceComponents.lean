import BenzelProblem6Kernel.TilingIncidenceGraph
import BenzelProblem6Kernel.SinkCandidateType

/-!
# Connected components of the tiling/owner incidence graph
-/

namespace BenzelProblem6Kernel

noncomputable instance incidenceConnectedComponentFintype {m : ℕ}
    (tiling : LiteralTiling m) :
    Fintype (tilingIncidenceGraph tiling).ConnectedComponent := by
  classical
  exact Fintype.ofSurjective
    (tilingIncidenceGraph tiling).connectedComponentMk Quot.mk_surjective

noncomputable def cellIncidenceComponent {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    (tilingIncidenceGraph tiling).ConnectedComponent :=
  (tilingIncidenceGraph tiling).connectedComponentMk
    (Sum.inr (chosenOwner (n := m + 5) (by omega) cell))

noncomputable def componentCells {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    Finset (BenzelCell (m + 5)) := by
  classical
  exact Finset.univ.filter fun cell =>
    cellIncidenceComponent tiling cell = component

noncomputable def componentPlacements {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    Finset (TilingPlacementNode tiling) := by
  classical
  exact Finset.univ.filter fun placement =>
    (tilingIncidenceGraph tiling).connectedComponentMk (Sum.inl placement) =
      component

noncomputable def componentOwners {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    Finset (SimplexPoint (m + 3)) := by
  classical
  exact Finset.univ.filter fun owner =>
    (tilingIncidenceGraph tiling).connectedComponentMk (Sum.inr owner) =
      component

theorem coveringPlacementNode_eq_of_covers {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5))
    (placement : TilingPlacementNode tiling)
    (hcover : PlacementCovers placement.1 cell) :
    coveringPlacementNode tiling cell = placement := by
  apply Subtype.ext
  exact ((tiling.2 cell).choose_spec.2 placement.1
    ⟨placement.2, hcover⟩).symm

theorem cell_component_eq_tile_component {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    cellIncidenceComponent tiling cell =
      (tilingIncidenceGraph tiling).connectedComponentMk
        (Sum.inl (coveringPlacementNode tiling cell)) := by
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (cell_tile_owner_adj tiling cell)).symm

theorem cell_component_eq_of_placement_covers {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5))
    (placement : TilingPlacementNode tiling)
    (hcover : PlacementCovers placement.1 cell) :
    cellIncidenceComponent tiling cell =
      (tilingIncidenceGraph tiling).connectedComponentMk
        (Sum.inl placement) := by
  rw [cell_component_eq_tile_component,
    coveringPlacementNode_eq_of_covers tiling cell placement hcover]

theorem cell_component_eq_owner_component {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    cellIncidenceComponent tiling cell =
      (tilingIncidenceGraph tiling).connectedComponentMk
        (Sum.inr (chosenOwner (n := m + 5) (by omega) cell)) := rfl

end BenzelProblem6Kernel
