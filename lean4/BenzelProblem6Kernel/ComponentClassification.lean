import BenzelProblem6Kernel.ComponentZeroEnergy
import Mathlib.Data.Fintype.Card

/-!
# The unique corner component and zero-corner component classification
-/

namespace BenzelProblem6Kernel

noncomputable def allCornerOwners (m : ℕ) : Finset (SimplexPoint (m + 3)) :=
  {sourceZero (m + 3), sourceOne (m + 3), sourceTwo (m + 3)}

theorem mem_allCornerOwners_iff {m : ℕ} (owner : SimplexPoint (m + 3)) :
    owner ∈ allCornerOwners m ↔ IsCornerOwner owner := by
  simp [allCornerOwners, IsCornerOwner, eq_comm]

theorem allCornerOwners_card (m : ℕ) : (allCornerOwners m).card = 3 := by
  classical
  have h01 : sourceZero (m + 3) ≠ sourceOne (m + 3) := by
    intro h
    have hv := congrArg SimplexPoint.v h
    simp [sourceZero, sourceOne] at hv
  have h02 : sourceZero (m + 3) ≠ sourceTwo (m + 3) := by
    intro h
    have hv := congrArg SimplexPoint.v h
    simp [sourceZero, sourceTwo] at hv
  have h12 : sourceOne (m + 3) ≠ sourceTwo (m + 3) := by
    intro h
    have hw := congrArg SimplexPoint.w h
    simp [sourceOne, sourceTwo] at hw
  simp [allCornerOwners, h01, h02, h12]

theorem componentCornerOwners_subset_all {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    componentCornerOwners tiling component ⊆ allCornerOwners m := by
  intro owner howner
  simp only [componentCornerOwners, Finset.mem_filter] at howner
  exact (mem_allCornerOwners_iff owner).2 howner.2

theorem componentCornerOwners_card_le_three {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    (componentCornerOwners tiling component).card ≤ 3 := by
  have hle := Finset.card_le_card
    (componentCornerOwners_subset_all tiling component)
  rw [allCornerOwners_card] at hle
  exact hle

noncomputable def cornerIncidenceComponent {m : ℕ} (tiling : LiteralTiling m) :
    (tilingIncidenceGraph tiling).ConnectedComponent :=
  (tilingIncidenceGraph tiling).connectedComponentMk
    (Sum.inr (sourceZero (m + 3)))

theorem sourceZero_mem_cornerComponentOwners {m : ℕ}
    (tiling : LiteralTiling m) :
    sourceZero (m + 3) ∈
      componentCornerOwners tiling (cornerIncidenceComponent tiling) := by
  classical
  simp only [componentCornerOwners, Finset.mem_filter, componentOwners,
    Finset.mem_univ, true_and]
  exact ⟨rfl, Or.inl rfl⟩

theorem cornerComponent_card_corners {m : ℕ} (tiling : LiteralTiling m) :
    (componentCornerOwners tiling (cornerIncidenceComponent tiling)).card = 3 := by
  have hpos := Finset.card_pos.mpr
    ⟨sourceZero (m + 3), sourceZero_mem_cornerComponentOwners tiling⟩
  obtain ⟨k, hk⟩ := three_dvd_componentCornerOwners_card tiling
    (cornerIncidenceComponent tiling)
  have hle := componentCornerOwners_card_le_three tiling
    (cornerIncidenceComponent tiling)
  omega

theorem cornerComponentOwners_eq_all {m : ℕ} (tiling : LiteralTiling m) :
    componentCornerOwners tiling (cornerIncidenceComponent tiling) =
      allCornerOwners m := by
  apply Finset.eq_of_subset_of_card_le
    (componentCornerOwners_subset_all tiling (cornerIncidenceComponent tiling))
  rw [cornerComponent_card_corners, allCornerOwners_card]

theorem corner_owner_component_eq {m : ℕ} (tiling : LiteralTiling m)
    (owner : SimplexPoint (m + 3)) (hcorner : IsCornerOwner owner) :
    (tilingIncidenceGraph tiling).connectedComponentMk (Sum.inr owner) =
      cornerIncidenceComponent tiling := by
  have hmem : owner ∈ componentCornerOwners tiling
      (cornerIncidenceComponent tiling) := by
    rw [cornerComponentOwners_eq_all]
    exact (mem_allCornerOwners_iff owner).2 hcorner
  simp only [componentCornerOwners, Finset.mem_filter, componentOwners,
    Finset.mem_univ, true_and] at hmem
  exact hmem.1

theorem component_eq_corner_of_has_corner {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent)
    (hcorners : (componentCornerOwners tiling component).card ≠ 0) :
    component = cornerIncidenceComponent tiling := by
  obtain ⟨owner, howner⟩ := Finset.card_ne_zero.mp hcorners
  have howner' := howner
  simp only [componentCornerOwners, Finset.mem_filter, componentOwners,
    Finset.mem_univ, true_and] at howner'
  exact howner'.1.symm.trans
    (corner_owner_component_eq tiling owner howner'.2)

theorem component_noCorners_of_ne_corner {m : ℕ}
    (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent)
    (hne : component ≠ cornerIncidenceComponent tiling) :
    (componentCornerOwners tiling component).card = 0 := by
  by_contra hnonzero
  exact hne (component_eq_corner_of_has_corner tiling component hnonzero)

theorem presentLabelFinset_nonempty {m : ℕ} (owner : SimplexPoint (m + 3)) :
    (presentLabelFinset owner).Nonempty := by
  rcases simplex_corner_or_full (t := m + 3) (by omega) owner with
    hzero | hone | htwo | hfull
  · subst owner
    have hcard := sourceZero_presentLabel_card m
    exact Finset.card_pos.mp (by omega)
  · subst owner
    have hcard := sourceOne_presentLabel_card m
    exact Finset.card_pos.mp (by omega)
  · subst owner
    have hcard := sourceTwo_presentLabel_card m
    exact Finset.card_pos.mp (by omega)
  · have hcard := full_owner_presentLabel_card owner hfull.1 hfull.2.1 hfull.2.2
    exact Finset.card_pos.mp (by omega)

theorem componentPlacements_nonempty {m : ℕ} (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    (componentPlacements tiling component).Nonempty := by
  classical
  obtain ⟨node, hnode⟩ := component.exists_rep
  rcases node with placement | owner
  · exact ⟨placement, by
      simp [componentPlacements]
      exact hnode⟩
  · obtain ⟨label, hlabel⟩ := presentLabelFinset_nonempty owner
    have hmem : inPeripheralBenzel (m + 5) (ownerCell owner label) := by
      simpa [presentLabelFinset] using hlabel
    let cell : BenzelCell (m + 5) := ⟨ownerCell owner label, hmem⟩
    let placement := coveringPlacementNode tiling cell
    refine ⟨placement, ?_⟩
    simp only [componentPlacements, Finset.mem_filter, Finset.mem_univ, true_and]
    have hadj := cell_tile_owner_adj tiling cell
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    have hchosen : chosenOwner (n := m + 5) (by omega) cell = owner := by
      let pair : PresentOwnerLabel (m + 5) := ⟨(owner, label), hmem⟩
      have hright := (benzelOwnerEquiv (n := m + 5) (by omega)).right_inv pair
      have hright' : chosenOwnerPair (n := m + 5) (by omega) cell = pair := by
        simpa [cell, pair, benzelOwnerEquiv] using hright
      exact congrArg (fun datum : PresentOwnerLabel (m + 5) => datum.1.1) hright'
    rw [hchosen] at heq
    exact heq.trans hnode

noncomputable def componentChosenPlacement {m : ℕ} (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    TilingPlacementNode tiling :=
  (componentPlacements_nonempty tiling component).choose

theorem componentChosenPlacement_mem {m : ℕ} (tiling : LiteralTiling m)
    (component : (tilingIncidenceGraph tiling).ConnectedComponent) :
    componentChosenPlacement tiling component ∈
      componentPlacements tiling component :=
  (componentPlacements_nonempty tiling component).choose_spec

noncomputable def inPhasePlacementFinset {m : ℕ} (tiling : LiteralTiling m) :
    Finset (TilingPlacementNode tiling) := by
  classical
  exact Finset.univ.filter fun placement => IsInPhaseStone placement.1

noncomputable def noncornerComponentEmbedding {m : ℕ} (tiling : LiteralTiling m) :
    {component : (tilingIncidenceGraph tiling).ConnectedComponent //
      component ≠ cornerIncidenceComponent tiling} ↪
      {placement : TilingPlacementNode tiling //
        placement ∈ inPhasePlacementFinset tiling} where
  toFun component := by
    let placement := componentChosenPlacement tiling component.1
    have hplacement := componentChosenPlacement_mem tiling component.1
    have hinphase := component_placements_inPhase_of_noCorners tiling component.1
      (component_noCorners_of_ne_corner tiling component.1 component.2)
      placement hplacement
    refine ⟨placement, ?_⟩
    simp only [inPhasePlacementFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hinphase
  inj' := by
    intro left right heq
    apply Subtype.ext
    have hvalue := congrArg (fun placement => placement.1.1) heq
    have hleft := componentChosenPlacement_mem tiling left.1
    have hright := componentChosenPlacement_mem tiling right.1
    simp only [componentPlacements, Finset.mem_filter, Finset.mem_univ,
      true_and] at hleft hright
    have hnode : (Sum.inl (componentChosenPlacement tiling left.1) :
        TilingIncidenceNode tiling) =
        Sum.inl (componentChosenPlacement tiling right.1) := by
      congr 1
      apply Subtype.ext
      exact hvalue
    rw [hnode] at hleft
    exact hleft.symm.trans hright

theorem card_components_le_inPhase_add_one {m : ℕ} (tiling : LiteralTiling m) :
    Fintype.card (tilingIncidenceGraph tiling).ConnectedComponent ≤
      (inPhasePlacementFinset tiling).card + 1 := by
  classical
  have hinj := Fintype.card_le_of_injective
    (noncornerComponentEmbedding tiling)
    (noncornerComponentEmbedding tiling).injective
  have hpartition := Fintype.card_subtype_compl
    (fun component : (tilingIncidenceGraph tiling).ConnectedComponent =>
      component = cornerIncidenceComponent tiling)
  have hcornerCard : Fintype.card
      {component : (tilingIncidenceGraph tiling).ConnectedComponent //
        component = cornerIncidenceComponent tiling} = 1 := by
    let equivalence :
        {component : (tilingIncidenceGraph tiling).ConnectedComponent //
          component = cornerIncidenceComponent tiling} ≃ Fin 1 :=
      { toFun := fun _ => 0
        invFun := fun _ => ⟨cornerIncidenceComponent tiling, rfl⟩
        left_inv := by intro component; apply Subtype.ext; exact component.2.symm
        right_inv := by intro index; exact (Fin.eq_zero index).symm }
    rw [Fintype.card_congr equivalence]
    simp
  have hnoncornerCard : Fintype.card
      {component : (tilingIncidenceGraph tiling).ConnectedComponent //
        component ≠ cornerIncidenceComponent tiling} =
      Fintype.card {component : (tilingIncidenceGraph tiling).ConnectedComponent //
        ¬component = cornerIncidenceComponent tiling} := rfl
  rw [hcornerCard] at hpartition
  have htarget : Fintype.card
      {placement : TilingPlacementNode tiling //
        placement ∈ inPhasePlacementFinset tiling} =
      (inPhasePlacementFinset tiling).card := Fintype.card_coe _
  rw [htarget] at hinj
  omega

end BenzelProblem6Kernel
