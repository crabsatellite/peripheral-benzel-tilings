import BenzelProblem6Kernel.ComponentPlacementCount

/-!
# Counting component cells by periodic owners and corner defects
-/

namespace BenzelProblem6Kernel

def ownerCellEmbedding {m : ℕ} (owner : SimplexPoint (m + 3)) :
    {label // label ∈ presentLabelFinset owner} ↪ BenzelCell (m + 5) where
  toFun label :=
    ⟨ownerCell owner label.1, by
      have h := label.2
      simp only [presentLabelFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      exact h⟩
  inj' := by
    rintro ⟨left, hleft⟩ ⟨right, hright⟩ heq
    apply Subtype.ext
    have hval := congrArg (fun cell : BenzelCell (m + 5) => cell.1) heq
    rcases left <;> rcases right <;>
      simp [ownerCell] at hval ⊢ <;> omega

noncomputable def ownerBenzelCells {m : ℕ} (owner : SimplexPoint (m + 3)) :
    Finset (BenzelCell (m + 5)) :=
  (presentLabelFinset owner).attach.map (ownerCellEmbedding owner)

theorem card_ownerBenzelCells {m : ℕ} (owner : SimplexPoint (m + 3)) :
    (ownerBenzelCells owner).card = (presentLabelFinset owner).card := by
  rw [ownerBenzelCells, Finset.card_map, Finset.card_attach]

theorem mem_ownerBenzelCells_iff {m : ℕ} (owner : SimplexPoint (m + 3))
    (cell : BenzelCell (m + 5)) :
    cell ∈ ownerBenzelCells owner ↔
      chosenOwner (n := m + 5) (by omega) cell = owner := by
  classical
  constructor
  · intro hmem
    simp only [ownerBenzelCells, Finset.mem_map, Finset.mem_attach] at hmem
    obtain ⟨label, _, heq⟩ := hmem
    have hcell := congrArg Subtype.val heq
    have hspec := chosenOwnerLabel_spec (n := m + 5) (by omega) cell
    obtain ⟨howner, _⟩ := owner_representation_unique cell.1
      (chosenOwner (n := m + 5) (by omega) cell) owner
      (chosenLabel (n := m + 5) (by omega) cell) label.1 hspec hcell
    exact howner
  · intro howner
    let label := chosenLabel (n := m + 5) (by omega) cell
    have hcell : ownerCell owner label = cell.1 := by
      rw [← howner]
      exact chosenOwnerLabel_spec (n := m + 5) (by omega) cell
    have hmem : inPeripheralBenzel (m + 5) (ownerCell owner label) := by
      rw [hcell]
      exact cell.2
    have hlabel : label ∈ presentLabelFinset owner := by
      simp [presentLabelFinset, hmem]
    simp only [ownerBenzelCells, Finset.mem_map, Finset.mem_attach]
    refine ⟨⟨label, hlabel⟩, by simp, ?_⟩
    apply Subtype.ext
    exact hcell

theorem cell_mem_component_iff_owner {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent)
    (cell : BenzelCell (m + 5)) :
    cell ∈ componentCells tiling component ↔
      chosenOwner (n := m + 5) (by omega) cell ∈
        componentOwners tiling component := by
  classical
  simp [componentCells, componentOwners, cellIncidenceComponent]

theorem component_cell_fiber_eq_ownerCells {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent)
    (owner : SimplexPoint (m + 3))
    (howner : owner ∈ componentOwners tiling component) :
    (componentCells tiling component).filter
        (fun cell => chosenOwner (n := m + 5) (by omega) cell = owner) =
      ownerBenzelCells owner := by
  classical
  ext cell
  simp only [Finset.mem_filter, mem_ownerBenzelCells_iff]
  constructor
  · exact fun h => h.2
  · intro hchosen
    refine ⟨?_, hchosen⟩
    apply (cell_mem_component_iff_owner tiling component cell).2
    rw [hchosen]
    exact howner

theorem componentCells_card_eq_sum_presentLabels {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    (componentCells tiling component).card =
      ∑ owner ∈ componentOwners tiling component,
        (presentLabelFinset owner).card := by
  classical
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := componentCells tiling component)
    (t := componentOwners tiling component)
    (f := chosenOwner (n := m + 5) (by omega))
    (fun cell hcell => (cell_mem_component_iff_owner tiling component cell).1 hcell)
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro owner howner
  rw [component_cell_fiber_eq_ownerCells tiling component owner howner,
    card_ownerBenzelCells]

def IsCornerOwner {m : ℕ} (owner : SimplexPoint (m + 3)) : Prop :=
  owner = sourceZero (m + 3) ∨ owner = sourceOne (m + 3) ∨
    owner = sourceTwo (m + 3)

noncomputable instance isCornerOwnerDecidable {m : ℕ}
    (owner : SimplexPoint (m + 3)) : Decidable (IsCornerOwner owner) :=
  Classical.propDecidable _

noncomputable def componentCornerOwners {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    Finset (SimplexPoint (m + 3)) := by
  classical
  exact (componentOwners tiling component).filter IsCornerOwner

theorem presentLabel_card_eq_three_sub_corner {m : ℕ}
    (owner : SimplexPoint (m + 3)) :
    (presentLabelFinset owner).card = if IsCornerOwner owner then 2 else 3 := by
  classical
  rcases simplex_corner_or_full (t := m + 3) (by omega) owner with
    hzero | hone | htwo | hfull
  · subst owner
    simp [IsCornerOwner, sourceZero_presentLabel_card]
  · subst owner
    simp [IsCornerOwner, sourceOne_presentLabel_card]
  · subst owner
    simp [IsCornerOwner, sourceTwo_presentLabel_card]
  · have hnot : ¬IsCornerOwner owner := by
      intro hcorner
      rcases hcorner with hzero | hone | htwo <;> subst owner <;>
        simp [sourceZero, sourceOne, sourceTwo] at hfull
    simp [hnot, full_owner_presentLabel_card owner hfull.1 hfull.2.1 hfull.2.2]

theorem componentCells_add_corners_eq_three_mul_owners {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    (componentCells tiling component).card +
        (componentCornerOwners tiling component).card =
      3 * (componentOwners tiling component).card := by
  classical
  rw [componentCells_card_eq_sum_presentLabels]
  simp_rw [presentLabel_card_eq_three_sub_corner]
  rw [componentCornerOwners, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ owner ∈ componentOwners tiling component,
        ((if IsCornerOwner owner then 2 else 3) +
          (if IsCornerOwner owner then 1 else 0))) =
        ∑ _owner ∈ componentOwners tiling component, 3 := by
      apply Finset.sum_congr rfl
      intro owner _
      split <;> omega
    _ = 3 * (componentOwners tiling component).card := by
      simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

theorem three_dvd_componentCornerOwners_card {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    3 ∣ (componentCornerOwners tiling component).card := by
  have htiles := componentCells_card_eq_three_mul_placements tiling component
  have howners := componentCells_add_corners_eq_three_mul_owners tiling component
  refine ⟨(componentOwners tiling component).card -
      (componentPlacements tiling component).card, ?_⟩
  omega

end BenzelProblem6Kernel
