import BenzelProblem6Kernel.ComponentOwnerCount

/-!
# Owner energy localized to incidence components
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

noncomputable def ownerPresentEnergyAt {m : ℕ}
    (owner : SimplexPoint (m + 3)) : ℤ :=
  (if inPeripheralBenzel (m + 5) (ownerCell owner .zero) then
      ownerLabelEnergy owner .zero else 0) +
  (if inPeripheralBenzel (m + 5) (ownerCell owner .one) then
      ownerLabelEnergy owner .one else 0) +
  (if inPeripheralBenzel (m + 5) (ownerCell owner .two) then
      ownerLabelEnergy owner .two else 0)

theorem literalCellEnergy_ownerCell {m : ℕ}
    (owner : SimplexPoint (m + 3)) (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5) (ownerCell owner label)) :
    literalCellEnergy (by omega : 5 ≤ m + 5)
        (⟨ownerCell owner label, hmem⟩ : BenzelCell (m + 5)) =
      ownerLabelEnergy owner label := by
  let pair : PresentOwnerLabel (m + 5) := ⟨(owner, label), hmem⟩
  have hright := (benzelOwnerEquiv (n := m + 5) (by omega)).right_inv pair
  have hright' : chosenOwnerPair (n := m + 5) (by omega)
      (⟨ownerCell owner label, hmem⟩ : BenzelCell (m + 5)) = pair := by
    simpa [benzelOwnerEquiv, pair] using hright
  change ownerLabelEnergy
      (chosenOwnerPair (n := m + 5) (by omega)
        (⟨ownerCell owner label, hmem⟩ : BenzelCell (m + 5))).1.1
      (chosenOwnerPair (n := m + 5) (by omega)
        (⟨ownerCell owner label, hmem⟩ : BenzelCell (m + 5))).1.2 = _
  rw [hright']

theorem ownerBenzelCells_energy_sum {m : ℕ}
    (owner : SimplexPoint (m + 3)) :
    ∑ cell ∈ ownerBenzelCells owner,
        literalCellEnergy (by omega : 5 ≤ m + 5) cell =
      ownerPresentEnergyAt owner := by
  classical
  rw [ownerBenzelCells, Finset.sum_map]
  calc
    (∑ label ∈ (presentLabelFinset owner).attach,
        literalCellEnergy (by omega : 5 ≤ m + 5)
          ((ownerCellEmbedding owner) label)) =
        ∑ label ∈ (presentLabelFinset owner).attach,
          ownerLabelEnergy owner label.1 := by
      apply Finset.sum_congr rfl
      intro label _
      apply literalCellEnergy_ownerCell
    _ = ownerPresentEnergyAt owner := by
      rw [Finset.sum_attach]
      have huniv : (Finset.univ : Finset MicroLabel) =
          {.zero, .one, .two} := by
        ext label
        rcases label <;> simp
      change (∑ label ∈ (Finset.univ : Finset MicroLabel).filter
          (fun label => inPeripheralBenzel (m + 5) (ownerCell owner label)),
            ownerLabelEnergy owner label) = ownerPresentEnergyAt owner
      rw [huniv]
      rw [Finset.sum_filter]
      by_cases hzero : inPeripheralBenzel (5 + m) (ownerCell owner .zero) <;>
        by_cases hone : inPeripheralBenzel (5 + m) (ownerCell owner .one) <;>
        by_cases htwo : inPeripheralBenzel (5 + m) (ownerCell owner .two) <;>
        simp [presentLabelFinset, hzero, hone, htwo,
          ownerPresentEnergyAt, Nat.add_comm] <;> ring

theorem component_tile_energy_eq_cell_energy {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    ∑ placement ∈ componentPlacements tiling component,
        literalPlacementEnergy placement.1 =
      ∑ cell ∈ componentCells tiling component,
        literalCellEnergy (by omega : 5 ≤ m + 5) cell := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun cell hcell =>
      (cell_mem_component_iff_coveringPlacement tiling component cell).1 hcell)]
  apply Finset.sum_congr rfl
  intro placement hplacement
  rw [component_cell_fiber_eq_placementCells tiling component placement
    hplacement]
  exact (placement_literal_cell_energy_sum placement.1).symm

theorem component_owner_energy_eq_cell_energy {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    ∑ owner ∈ componentOwners tiling component, ownerPresentEnergyAt owner =
      ∑ cell ∈ componentCells tiling component,
        literalCellEnergy (by omega : 5 ≤ m + 5) cell := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun cell hcell =>
      (cell_mem_component_iff_owner tiling component cell).1 hcell)]
  apply Finset.sum_congr rfl
  intro owner howner
  rw [component_cell_fiber_eq_ownerCells tiling component owner howner]
  exact (ownerBenzelCells_energy_sum owner).symm

theorem component_tile_energy_eq_owner_energy {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    ∑ placement ∈ componentPlacements tiling component,
        literalPlacementEnergy placement.1 =
      ∑ owner ∈ componentOwners tiling component,
        ownerPresentEnergyAt owner := by
  rw [component_tile_energy_eq_cell_energy,
    component_owner_energy_eq_cell_energy]

theorem ownerPresentEnergyAt_corner_or_zero {m : ℕ}
    (owner : SimplexPoint (m + 3)) :
    ownerPresentEnergyAt owner =
      if IsCornerOwner owner then (m + 3 : ℤ) else 0 := by
  classical
  rcases simplex_corner_or_full (t := m + 3) (by omega) owner with
    hzero | hone | htwo | hfull
  · subst owner
    simp [IsCornerOwner, ownerPresentEnergyAt, owner_zero_mem_iff,
      owner_one_mem_iff, owner_two_mem_iff, sourceZero,
      ownerLabelEnergy, ownerPotential, ownerQ, ownerR]
  · subst owner
    simp [IsCornerOwner, ownerPresentEnergyAt, owner_zero_mem_iff,
      owner_one_mem_iff, owner_two_mem_iff, sourceOne,
      ownerLabelEnergy, ownerPotential, ownerQ, ownerR]
  · subst owner
    simp [IsCornerOwner, ownerPresentEnergyAt, owner_zero_mem_iff,
      owner_one_mem_iff, owner_two_mem_iff, sourceTwo,
      ownerLabelEnergy, ownerPotential, ownerQ, ownerR]
    ring
  · have hz := (owner_zero_mem_iff (n := m + 5) (by omega) owner).2 hfull.2.1
    have ho := (owner_one_mem_iff (n := m + 5) (by omega) owner).2 hfull.2.2
    have ht := (owner_two_mem_iff (n := m + 5) (by omega) owner).2 hfull.1
    have hnot : ¬IsCornerOwner owner := by
      intro hcorner
      rcases hcorner with h0 | h1 | h2 <;> subst owner <;>
        simp [sourceZero, sourceOne, sourceTwo] at hfull
    simp [hnot, ownerPresentEnergyAt, hz, ho, ht,
      ownerLabelEnergy, ownerPotential_sum]

theorem component_owner_energy_eq_corners {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    ∑ owner ∈ componentOwners tiling component,
        ownerPresentEnergyAt owner =
      ((m + 3 : ℕ) : ℤ) * (componentCornerOwners tiling component).card := by
  classical
  simp_rw [ownerPresentEnergyAt_corner_or_zero]
  rw [componentCornerOwners, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro owner _
  split <;> simp_all

theorem component_tile_energy_eq_corners {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    ∑ placement ∈ componentPlacements tiling component,
        literalPlacementEnergy placement.1 =
      ((m + 3 : ℕ) : ℤ) * (componentCornerOwners tiling component).card := by
  rw [component_tile_energy_eq_owner_energy,
    component_owner_energy_eq_corners]

end BenzelProblem6Kernel
