import FiniteDefects.D4ReverseStone

/-! # Reconstructing one literal good bone from one abstract labelled step -/

namespace FiniteDefects

def reverseBoneBase {t : ℕ} (source : SimplexPoint t)
    (boneClass : GoodBoneClass) : Cell :=
  (ownerQ source - boneClass.sourceShift.1,
    ownerR source - boneClass.sourceShift.2)

theorem reverseBoneBase_source_anchor {t : ℕ} (source : SimplexPoint t)
    (boneClass : GoodBoneClass) :
    ((reverseBoneBase source boneClass).1 + boneClass.sourceShift.1,
      (reverseBoneBase source boneClass).2 + boneClass.sourceShift.2) =
      (ownerQ source, ownerR source) := by
  simp [reverseBoneBase]

theorem reverseBoneBase_target_anchor {t : ℕ}
    (source target : SimplexPoint t) (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target)) :
    ((reverseBoneBase source boneClass).1 + boneClass.targetShift.1,
      (reverseBoneBase source boneClass).2 + boneClass.targetShift.2) =
      (ownerQ target, ownerR target) := by
  have hclass := goodBoneClass_target boneClass
  have hsource := reverseBoneBase_source_anchor source boneClass
  rw [← hsource] at hstep
  apply Prod.ext
  · have hc := congrArg Prod.fst hclass
    have hs := congrArg Prod.fst hstep
    simp [addCell] at hc hs ⊢
    omega
  · have hc := congrArg Prod.snd hclass
    have hs := congrArg Prod.snd hstep
    simp [addCell] at hc hs ⊢
    omega

theorem reverseBone_local_cell_eq {m : ℕ}
    (source target : SimplexPoint (m + 2))
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
  rcases goodBoneClass_cell_role boneClass localCell hlocal with hsource | htarget
  · left
    refine ⟨localLabel boneClass.residue localCell, hsource.2, rfl, ?_⟩
    rw [ownerCell_eq_cellForOwnerAnchor]
    have hbase := reverseBoneBase_source_anchor source boneClass
    rw [← hbase]
    have hanchor := ownerAnchorForCell_translate_eq
      (reverseBoneBase source boneClass) boneClass.residue localCell
    rw [hsource.1] at hanchor
    rw [← hanchor]
    exact (cell_anchor_roundtrip _ _).symm
  · right
    refine ⟨htarget.2, ?_⟩
    rw [ownerCell_eq_cellForOwnerAnchor]
    have hbase := reverseBoneBase_target_anchor source target boneClass hstep
    rw [← hbase]
    have hanchor := ownerAnchorForCell_translate_eq
      (reverseBoneBase source boneClass) boneClass.residue localCell
    rw [htarget.1] at hanchor
    rw [← hanchor, ← htarget.2]
    exact (cell_anchor_roundtrip _ _).symm

noncomputable def d4ReverseBonePlacement {m : ℕ}
    (source target : SimplexPoint (m + 2))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inBenzel (m + 4) (2 * m + 4) (ownerCell source label))
    (htargetMem : inBenzel (m + 4) (2 * m + 4)
      (ownerCell target boneClass.label)) : D4LiteralPlacement m := by
  let base := reverseBoneBase source boneClass
  have hall : ∀ localCell ∈ protoCells boneClass.tile,
      inBenzel (m + 4) (2 * m + 4)
        (translateLocalCell base localCell) := by
    intro localCell hlocal
    rcases reverseBone_local_cell_eq source target boneClass hstep
      localCell hlocal with ⟨label, hne, _, heq⟩ | ⟨_, heq⟩
    · rw [heq]
      exact hsourceMem label hne
    · rw [heq]
      exact htargetMem
  have hbaseMem : inBenzel (m + 4) (2 * m + 4) base := by
    have h := hall c00 (by rcases boneClass <;> simp [GoodBoneClass.tile, protoCells])
    simpa [base, translateLocalCell, c00] using h
  let baseCell : D4Cell m := ⟨base, hbaseMem⟩
  let candidate : D4PlacementCandidate m := (boneClass.tile, baseCell)
  exact ⟨candidate, by
    intro cell hcell
    change cell ∈ (protoCells boneClass.tile).map
      (translateLocalCell base) at hcell
    simp only [List.mem_map] at hcell
    obtain ⟨localCell, hlocal, rfl⟩ := hcell
    exact hall localCell hlocal⟩

@[simp] theorem d4ReverseBonePlacement_tile {m : ℕ}
    (source target : SimplexPoint (m + 2)) (boneClass : GoodBoneClass)
    (hstep) (hsourceMem) (htargetMem) :
    (d4ReverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem).tile = boneClass.tile := rfl

@[simp] theorem d4ReverseBonePlacement_base {m : ℕ}
    (source target : SimplexPoint (m + 2)) (boneClass : GoodBoneClass)
    (hstep) (hsourceMem) (htargetMem) :
    (d4ReverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem).base = reverseBoneBase source boneClass := rfl

end FiniteDefects
