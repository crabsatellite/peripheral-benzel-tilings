import BenzelProblem6Kernel.ReverseBoneClass

/-!
# Reconstructing one literal placement from one abstract labelled edge
-/

namespace BenzelProblem6Kernel

theorem c00_mem_protoCells (tile : ProtoTile) : c00 ∈ protoCells tile := by
  rcases tile <;> simp [protoCells]

theorem reverseBone_local_cell_eq {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (localCell : LocalCell) (hlocal : localCell ∈ protoCells boneClass.tile) :
    (∃ label, label ≠ boneClass.label ∧
      localLabel boneClass.residue localCell = label ∧
      translateLocalCell (reverseBoneBase source boneClass) localCell =
        ownerCell source label) ∨
    (localLabel boneClass.residue localCell = boneClass.label ∧
      translateLocalCell (reverseBoneBase source boneClass) localCell =
        ownerCell target boneClass.label) := by
  have hrole := goodBoneClass_cell_role boneClass localCell hlocal
  rcases hrole with hsource | htarget
  · left
    refine ⟨localLabel boneClass.residue localCell, hsource.2, rfl, ?_⟩
    rw [ownerCell_eq_cellForOwnerAnchor]
    have hbase := reverseBoneBase_source_anchor source boneClass
    rw [← hbase]
    have hanchor := ownerAnchorForCell_translate_eq
      (reverseBoneBase source boneClass) boneClass.residue localCell
    have hshift := hsource.1
    change ownerShift boneClass.residue localCell = boneClass.sourceShift at hshift
    rw [hshift] at hanchor
    rw [← hanchor]
    exact (cell_anchor_roundtrip _ _).symm
  · right
    refine ⟨htarget.2, ?_⟩
    rw [ownerCell_eq_cellForOwnerAnchor]
    have hbase := reverseBoneBase_target_anchor source target boneClass hstep
    rw [← hbase]
    have hanchor := ownerAnchorForCell_translate_eq
      (reverseBoneBase source boneClass) boneClass.residue localCell
    have hshift := htarget.1
    change ownerShift boneClass.residue localCell = boneClass.targetShift at hshift
    rw [hshift] at hanchor
    have hlabel : localLabel boneClass.residue localCell = boneClass.label :=
      htarget.2
    rw [← hanchor, ← hlabel]
    exact (cell_anchor_roundtrip _ _).symm

noncomputable def reverseBonePlacement {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) : LiteralPlacement m := by
  let base := reverseBoneBase source boneClass
  have hall : ∀ localCell ∈ protoCells boneClass.tile,
      inPeripheralBenzel (m + 5) (translateLocalCell base localCell) := by
    intro localCell hlocal
    have hrole := reverseBone_local_cell_eq source target boneClass hstep
      localCell hlocal
    rcases hrole with ⟨label, hne, _, heq⟩ | ⟨_, heq⟩
    · rw [heq]
      exact hsourceMem label hne
    · rw [heq]
      exact htargetMem
  have hbaseMem : inPeripheralBenzel (m + 5) base := by
    have h := hall c00 (c00_mem_protoCells boneClass.tile)
    simpa [base, translateLocalCell, c00] using h
  let baseCell : BenzelCell (m + 5) := ⟨base, hbaseMem⟩
  let candidate : PlacementCandidate m := (boneClass.tile, baseCell)
  exact ⟨candidate, by
    intro cell hcell
    change cell ∈ (protoCells boneClass.tile).map (translateLocalCell base) at hcell
    simp only [List.mem_map] at hcell
    obtain ⟨localCell, hlocal, rfl⟩ := hcell
    exact hall localCell hlocal⟩

end BenzelProblem6Kernel
