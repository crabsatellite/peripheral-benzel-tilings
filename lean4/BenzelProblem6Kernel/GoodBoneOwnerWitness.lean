import BenzelProblem6Kernel.GoodBoneClasses

/-!
# Literal owner witnesses for the six good bone classes
-/

namespace BenzelProblem6Kernel

def GoodBoneClass.sourceWitnessLabel : GoodBoneClass → MicroLabel
  | .boneA0 | .boneA2 | .boneB0 | .boneB1 => .zero
  | .boneC0 | .boneC2 => .one

def GoodBoneClass.sourceWitnessCell : GoodBoneClass → LocalCell
  | .boneA0 | .boneB0 => c00
  | .boneA2 => c10
  | .boneB1 => c01
  | .boneC0 => c2m2
  | .boneC2 => c1m1

def GoodBoneClass.targetWitnessCell : GoodBoneClass → LocalCell
  | .boneA0 => c20
  | .boneA2 | .boneB1 | .boneC0 => c00
  | .boneB0 => c02
  | .boneC2 => c2m2

theorem sourceWitnessCell_mem (boneClass : GoodBoneClass) :
    boneClass.sourceWitnessCell ∈ protoCells boneClass.tile := by
  rcases boneClass <;> decide

theorem targetWitnessCell_mem (boneClass : GoodBoneClass) :
    boneClass.targetWitnessCell ∈ protoCells boneClass.tile := by
  rcases boneClass <;> decide

theorem sourceWitness_anchor (boneClass : GoodBoneClass) (base : Cell) :
    cellForOwnerAnchor
        (base.1 + boneClass.sourceShift.1,
          base.2 + boneClass.sourceShift.2)
        boneClass.sourceWitnessLabel =
      translateLocalCell base boneClass.sourceWitnessCell := by
  rcases boneClass <;>
    simp [GoodBoneClass.sourceShift, GoodBoneClass.sourceWitnessLabel,
      GoodBoneClass.sourceWitnessCell, cellForOwnerAnchor,
      translateLocalCell, c00, c10, c01, c1m1, c2m2]
  all_goals omega

theorem targetWitness_anchor (boneClass : GoodBoneClass) (base : Cell) :
    cellForOwnerAnchor
        (base.1 + boneClass.targetShift.1,
          base.2 + boneClass.targetShift.2)
        boneClass.label =
      translateLocalCell base boneClass.targetWitnessCell := by
  rcases boneClass <;>
    simp [GoodBoneClass.targetShift, GoodBoneClass.label,
      GoodBoneClass.targetWitnessCell, cellForOwnerAnchor,
      translateLocalCell, c00, c20, c02, c2m2, stepA, stepC]

theorem goodBone_source_phase {m : ℕ} (placement : LiteralPlacement m)
    (boneClass : GoodBoneClass) (hclass : IsPlacementClass placement boneClass) :
    IsOwnerPhase (m + 3)
      (placement.base.1 + boneClass.sourceShift.1,
        placement.base.2 + boneClass.sourceShift.2) := by
  have hbase := placementBaseResidue_spec (m + 3) placement.base
  unfold BaseHasResidue at hbase
  rw [hclass.2] at hbase
  rcases boneClass <;>
    simp only [GoodBoneClass.residue, Res3.value,
      GoodBoneClass.sourceShift] at hbase ⊢ <;>
    apply shifted_anchor_is_phase hbase <;> norm_num

theorem goodBone_target_phase {m : ℕ} (placement : LiteralPlacement m)
    (boneClass : GoodBoneClass) (hclass : IsPlacementClass placement boneClass) :
    IsOwnerPhase (m + 3)
      (placement.base.1 + boneClass.targetShift.1,
        placement.base.2 + boneClass.targetShift.2) := by
  have hbase := placementBaseResidue_spec (m + 3) placement.base
  unfold BaseHasResidue at hbase
  rw [hclass.2] at hbase
  rcases boneClass <;>
    simp only [GoodBoneClass.residue, Res3.value,
      GoodBoneClass.targetShift, stepA, stepC] at hbase ⊢ <;>
    apply shifted_anchor_is_phase hbase <;> norm_num

theorem sourceWitness_mem_benzel {m : ℕ} (placement : LiteralPlacement m)
    (boneClass : GoodBoneClass) (hclass : IsPlacementClass placement boneClass) :
    inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (placement.base.1 + boneClass.sourceShift.1,
          placement.base.2 + boneClass.sourceShift.2)
        boneClass.sourceWitnessLabel) := by
  rw [sourceWitness_anchor]
  apply placement.2
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
  exact ⟨boneClass.sourceWitnessCell,
    by
      change boneClass.sourceWitnessCell ∈ protoCells placement.tile
      rw [hclass.1]
      exact sourceWitnessCell_mem boneClass,
    rfl⟩

theorem targetWitness_mem_benzel {m : ℕ} (placement : LiteralPlacement m)
    (boneClass : GoodBoneClass) (hclass : IsPlacementClass placement boneClass) :
    inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (placement.base.1 + boneClass.targetShift.1,
          placement.base.2 + boneClass.targetShift.2)
        boneClass.label) := by
  rw [targetWitness_anchor]
  apply placement.2
  simp only [LiteralPlacement.cells, placementCellList, List.mem_map]
  exact ⟨boneClass.targetWitnessCell,
    by
      change boneClass.targetWitnessCell ∈ protoCells placement.tile
      rw [hclass.1]
      exact targetWitnessCell_mem boneClass,
    rfl⟩

theorem exists_goodBone_source_simplex {m : ℕ}
    (placement : LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : IsPlacementClass placement boneClass) :
    ∃ p : SimplexPoint (m + 3),
      ownerQ p = placement.base.1 + boneClass.sourceShift.1 ∧
      ownerR p = placement.base.2 + boneClass.sourceShift.2 := by
  simpa [show m + 5 - 2 = m + 3 by omega] using
    phase_anchor_has_simplex (n := m + 5) (by omega)
      (placement.base.1 + boneClass.sourceShift.1,
        placement.base.2 + boneClass.sourceShift.2)
      boneClass.sourceWitnessLabel
      (goodBone_source_phase placement boneClass hclass)
      (sourceWitness_mem_benzel placement boneClass hclass)

theorem exists_goodBone_target_simplex {m : ℕ}
    (placement : LiteralPlacement m) (boneClass : GoodBoneClass)
    (hclass : IsPlacementClass placement boneClass) :
    ∃ p : SimplexPoint (m + 3),
      ownerQ p = placement.base.1 + boneClass.targetShift.1 ∧
      ownerR p = placement.base.2 + boneClass.targetShift.2 := by
  simpa [show m + 5 - 2 = m + 3 by omega] using
    phase_anchor_has_simplex (n := m + 5) (by omega)
      (placement.base.1 + boneClass.targetShift.1,
        placement.base.2 + boneClass.targetShift.2)
      boneClass.label
      (goodBone_target_phase placement boneClass hclass)
      (targetWitness_mem_benzel placement boneClass hclass)

end BenzelProblem6Kernel
