import BenzelProblem6Kernel.TerminalBonePlacements

/-!
# Exact owner roles of a reconstructed bone
-/

namespace BenzelProblem6Kernel

@[simp] theorem reverseBonePlacement_tile {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) :
    (reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem).tile = boneClass.tile := by
  rfl

@[simp] theorem reverseBonePlacement_base {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) :
    (reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem).base = reverseBoneBase source boneClass := by
  rfl

theorem reverseBonePlacement_covers_source {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (label : MicroLabel) (hne : label ≠ boneClass.label) :
    PlacementCovers
      (reverseBonePlacement source target boneClass hstep
        hsourceMem htargetMem)
      ⟨ownerCell source label, hsourceMem label hne⟩ := by
  obtain ⟨localCell, hlocal, heq⟩ :=
    exists_source_label_witness boneClass (reverseBoneBase source boneClass)
      label hne
  have hanchor := reverseBoneBase_source_anchor source boneClass
  have howner : ownerCell source label =
      cellForOwnerAnchor
        ((reverseBoneBase source boneClass).1 + boneClass.sourceShift.1,
          (reverseBoneBase source boneClass).2 + boneClass.sourceShift.2) label := by
    rw [ownerCell_eq_cellForOwnerAnchor, ← hanchor]
  change ownerCell source label ∈
    (protoCells boneClass.tile).map
      (translateLocalCell (reverseBoneBase source boneClass))
  rw [howner, heq]
  simp only [List.mem_map]
  exact ⟨localCell, hlocal, rfl⟩

theorem reverseBonePlacement_covers_target {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) :
    PlacementCovers
      (reverseBonePlacement source target boneClass hstep
        hsourceMem htargetMem)
      ⟨ownerCell target boneClass.label, htargetMem⟩ := by
  let base := reverseBoneBase source boneClass
  have hbase := reverseBoneBase_target_anchor source target boneClass hstep
  have hwitness := targetWitness_anchor boneClass base
  have heq : ownerCell target boneClass.label =
      translateLocalCell base boneClass.targetWitnessCell := by
    rw [ownerCell_eq_cellForOwnerAnchor, ← hbase]
    exact hwitness
  change ownerCell target boneClass.label ∈
    (protoCells boneClass.tile).map (translateLocalCell base)
  rw [heq]
  simp only [List.mem_map]
  exact ⟨boneClass.targetWitnessCell, targetWitnessCell_mem boneClass, rfl⟩

theorem reverseBonePlacement_cover_role {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (cell : Cell)
    (hcover : cell ∈
      (reverseBonePlacement source target boneClass hstep
        hsourceMem htargetMem).cells) :
    (∃ label, label ≠ boneClass.label ∧ cell = ownerCell source label) ∨
      cell = ownerCell target boneClass.label := by
  change cell ∈ (protoCells boneClass.tile).map
    (translateLocalCell (reverseBoneBase source boneClass)) at hcover
  simp only [List.mem_map] at hcover
  obtain ⟨localCell, hlocal, rfl⟩ := hcover
  have hrole := reverseBone_local_cell_eq source target boneClass hstep
    localCell hlocal
  rcases hrole with ⟨label, hne, _, heq⟩ | ⟨_, heq⟩
  · exact Or.inl ⟨label, hne, heq⟩
  · exact Or.inr heq

end BenzelProblem6Kernel
