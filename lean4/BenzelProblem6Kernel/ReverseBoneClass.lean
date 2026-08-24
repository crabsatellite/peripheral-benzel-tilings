import BenzelProblem6Kernel.LiteralYToPathModel

/-!
# The unique good bone class determined by a label and ballot move
-/

namespace BenzelProblem6Kernel

def goodBoneClassOfMove : MicroLabel → BallotMove → GoodBoneClass
  | .zero, .majority => .boneC0
  | .zero, .minority => .boneC2
  | .one, .majority => .boneB1
  | .one, .minority => .boneB0
  | .two, .majority => .boneA0
  | .two, .minority => .boneA2

@[simp] theorem goodBoneClassOfMove_label (label : MicroLabel)
    (move : BallotMove) :
    (goodBoneClassOfMove label move).label = label := by
  rcases label <;> rcases move <;> rfl

@[simp] theorem goodBoneClassOfMove_ballotMove (label : MicroLabel)
    (move : BallotMove) :
    (goodBoneClassOfMove label move).ballotMove = move := by
  rcases label <;> rcases move <;> rfl

theorem goodBoneClassOfMove_step (label : MicroLabel) (move : BallotMove) :
    (goodBoneClassOfMove label move).step =
      match label, move with
      | .zero, .majority => stepC
      | .zero, .minority => stepA
      | .one, .majority => stepB
      | .one, .minority => stepC
      | .two, .majority => stepA
      | .two, .minority => stepB := by
  rcases label <;> rcases move <;> rfl

theorem goodBoneClassOfMove_unique (boneClass : GoodBoneClass) :
    goodBoneClassOfMove boneClass.label boneClass.ballotMove = boneClass := by
  rcases boneClass <;> rfl

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

theorem reverseBoneBase_target_anchor {t : ℕ} (source target : SimplexPoint t)
    (boneClass : GoodBoneClass)
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

end BenzelProblem6Kernel
