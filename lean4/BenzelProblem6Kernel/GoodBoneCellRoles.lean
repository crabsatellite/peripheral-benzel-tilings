import BenzelProblem6Kernel.GoodBoneClasses

/-!
# Source/target role of every cell in a good bone
-/

namespace BenzelProblem6Kernel

theorem goodBoneClass_cell_role (boneClass : GoodBoneClass)
    (localCell : LocalCell) (hlocal : localCell ∈ protoCells boneClass.tile) :
    let datum := localOwnerDatum boneClass.residue localCell
    (datum.1 = boneClass.sourceShift ∧ datum.2 ≠ boneClass.label) ∨
      (datum.1 = boneClass.targetShift ∧ datum.2 = boneClass.label) := by
  rcases boneClass <;>
    simp [GoodBoneClass.tile, GoodBoneClass.residue, GoodBoneClass.sourceShift,
      GoodBoneClass.targetShift, GoodBoneClass.label, protoCells] at hlocal
  all_goals rcases hlocal with rfl | rfl | rfl <;> decide

theorem goodBoneClass_source_labels (boneClass : GoodBoneClass) :
    List.Perm
      ((boneOwnerProfile boneClass.tile boneClass.residue).filter
        (fun datum => datum.1 = boneClass.sourceShift))
      (([.zero, .one, .two].filter fun label => label ≠ boneClass.label).map
        (fun label => (boneClass.sourceShift, label))) := by
  rcases boneClass <;> decide

theorem goodBoneClass_target_label (boneClass : GoodBoneClass) :
    (boneOwnerProfile boneClass.tile boneClass.residue).filter
        (fun datum => datum.1 = boneClass.targetShift) =
      [(boneClass.targetShift, boneClass.label)] := by
  rcases boneClass <;> decide

end BenzelProblem6Kernel
