import FiniteDefects.D4ActiveCounts

/-! # Good-edge sources plus the three boundary owners exhaust active owners -/

namespace FiniteDefects

noncomputable def d4EdgeSourceSet {m : ℕ} (tiling : D4LiteralTiling m) :
    Finset (SimplexPoint (m + 2)) :=
  Finset.univ.image (fun edge : D4GoodBonePlacement tiling => edge.source)

noncomputable def d4BoundaryOwnerSet (m : ℕ) :
    Finset (SimplexPoint (m + 2)) :=
  Finset.univ.image (d4BoundaryOwner m)

noncomputable def d4ActiveOwnerSet {m : ℕ} (tiling : D4LiteralTiling m) :
    Finset (SimplexPoint (m + 2)) := by
  classical
  exact Finset.univ.filter (IsD4ActiveOwner tiling)

theorem card_d4EdgeSourceSet {m : ℕ} (tiling : D4LiteralTiling m) :
    (d4EdgeSourceSet tiling).card =
      Fintype.card (D4GoodBonePlacement tiling) := by
  rw [d4EdgeSourceSet, Finset.card_image_of_injective]
  · simp
  · exact fun left right h => d4TilingEdge_source_unique left right h

theorem card_d4BoundaryOwnerSet (m : ℕ) :
    (d4BoundaryOwnerSet m).card = 3 := by
  rw [d4BoundaryOwnerSet, Finset.card_image_of_injective]
  · decide
  · exact d4BoundaryOwner_injective m

theorem card_d4ActiveOwnerSet {m : ℕ} (tiling : D4LiteralTiling m) :
    (d4ActiveOwnerSet tiling).card =
      Fintype.card (D4ActiveOwner tiling) := by
  classical
  let equiv : D4ActiveOwner tiling ≃ ↥(d4ActiveOwnerSet tiling) :=
    { toFun := fun p => ⟨p.1, by
        unfold d4ActiveOwnerSet
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ p.1, p.2⟩⟩
      invFun := fun p => ⟨p.1, by
        unfold d4ActiveOwnerSet at p
        exact (Finset.mem_filter.mp p.2).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  rw [← Fintype.card_coe (d4ActiveOwnerSet tiling),
    Fintype.card_congr equiv]

theorem d4Edge_source_active {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    IsD4ActiveOwner tiling edge.source := by
  intro hstoneMem
  simp only [d4StoneOwnerSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hstoneMem
  obtain ⟨stone, howner⟩ := hstoneMem
  obtain ⟨other, hother, _⟩ := microLabel_exists_ne_two edge.label edge.label
  have hpresent := d4TilingEdge_source_full edge other
  have hedgeCover := d4TilingEdge_covers_source_other edge other hother hpresent
  have hstonePresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell stone.owner other) := stone.owner_full other
  have hstoneCover := d4Stone_covers_owner_label stone.1 stone.2.2.1
    stone.2.2.2 other hstonePresent
  have hedgeEq := d4CoveringPlacement_unique tiling
    ⟨ownerCell edge.source other, hpresent⟩ edge.1 edge.2.1 hedgeCover
  have hstoneEq := d4CoveringPlacement_unique tiling
    ⟨ownerCell edge.source other, hpresent⟩ stone.1 stone.2.1 (by
      have hcellEq :
          (⟨ownerCell stone.owner other, hstonePresent⟩ : D4Cell m) =
            ⟨ownerCell edge.source other, hpresent⟩ := by
        apply Subtype.ext
        change ownerCell stone.owner other = ownerCell edge.source other
        rw [howner]
      rw [← hcellEq]
      exact hstoneCover)
  have heq : edge.1 = stone.1 := hedgeEq.trans hstoneEq.symm
  exact edge.2.2.1 (by simpa [heq] using stone.2.2.1)

theorem d4Edge_target_active {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    IsD4ActiveOwner tiling edge.target := by
  intro hstoneMem
  simp only [d4StoneOwnerSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hstoneMem
  obtain ⟨stone, howner⟩ := hstoneMem
  have hpresent := d4GoodEdge_target_present edge.edge
  have hedgeCover := d4TilingEdge_covers_target edge hpresent
  have hstonePresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell stone.owner edge.label) := stone.owner_full edge.label
  have hstoneCover := d4Stone_covers_owner_label stone.1 stone.2.2.1
    stone.2.2.2 edge.label hstonePresent
  have hedgeEq := d4CoveringPlacement_unique tiling
    ⟨ownerCell edge.target edge.label, hpresent⟩ edge.1 edge.2.1 hedgeCover
  have hstoneEq := d4CoveringPlacement_unique tiling
    ⟨ownerCell edge.target edge.label, hpresent⟩ stone.1 stone.2.1 (by
      have hcellEq :
          (⟨ownerCell stone.owner edge.label, hstonePresent⟩ : D4Cell m) =
            ⟨ownerCell edge.target edge.label, hpresent⟩ := by
        apply Subtype.ext
        change ownerCell stone.owner edge.label = ownerCell edge.target edge.label
        rw [howner]
      rw [← hcellEq]
      exact hstoneCover)
  have heq : edge.1 = stone.1 := hedgeEq.trans hstoneEq.symm
  exact edge.2.2.1 (by simpa [heq] using stone.2.2.1)

theorem d4Boundary_active {m : ℕ} (tiling : D4LiteralTiling m)
    (label : MicroLabel) :
    IsD4ActiveOwner tiling (d4BoundaryOwner m label) := by
  intro hstoneMem
  simp only [d4StoneOwnerSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hstoneMem
  obtain ⟨stone, howner⟩ := hstoneMem
  obtain ⟨other, hne, _⟩ := microLabel_exists_ne_two label label
  have hotherPresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell (d4BoundaryOwner m label) other) := by
    simpa [howner] using stone.owner_full other
  exact hne ((d4BoundaryOwner_present_iff m label other).1 hotherPresent)

theorem d4Boundary_not_edge_source {m : ℕ}
    {tiling : D4LiteralTiling m} (label : MicroLabel)
    (edge : D4GoodBonePlacement tiling) :
    edge.source ≠ d4BoundaryOwner m label := by
  intro hsource
  obtain ⟨other, hne, _⟩ := microLabel_exists_ne_two label label
  have hpresent := d4TilingEdge_source_full edge other
  have : other = label :=
    (d4BoundaryOwner_present_iff m label other).1 (by
      simpa [hsource] using hpresent)
  exact hne this

theorem d4EdgeSourceSet_subset_active {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4EdgeSourceSet tiling ⊆ d4ActiveOwnerSet tiling := by
  intro p hp
  simp only [d4EdgeSourceSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hp
  obtain ⟨edge, rfl⟩ := hp
  simp [d4ActiveOwnerSet, d4Edge_source_active edge]

theorem d4BoundaryOwnerSet_subset_active {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4BoundaryOwnerSet m ⊆ d4ActiveOwnerSet tiling := by
  intro p hp
  simp only [d4BoundaryOwnerSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hp
  obtain ⟨label, rfl⟩ := hp
  simp [d4ActiveOwnerSet, d4Boundary_active tiling label]

theorem d4Source_boundary_disjoint {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Disjoint (d4EdgeSourceSet tiling) (d4BoundaryOwnerSet m) := by
  rw [Finset.disjoint_left]
  intro p hsource hboundary
  simp only [d4EdgeSourceSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hsource
  simp only [d4BoundaryOwnerSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hboundary
  obtain ⟨edge, rfl⟩ := hsource
  obtain ⟨label, hlabel⟩ := hboundary
  exact d4Boundary_not_edge_source label edge hlabel.symm

theorem d4_source_union_boundary_eq_active {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4EdgeSourceSet tiling ∪ d4BoundaryOwnerSet m =
      d4ActiveOwnerSet tiling := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.union_subset
      (d4EdgeSourceSet_subset_active tiling)
      (d4BoundaryOwnerSet_subset_active tiling)
  · rw [Finset.card_union_of_disjoint (d4Source_boundary_disjoint tiling),
      card_d4EdgeSourceSet, card_d4BoundaryOwnerSet,
      card_d4ActiveOwnerSet, card_active_eq_goodEdges_add_three]

end FiniteDefects
