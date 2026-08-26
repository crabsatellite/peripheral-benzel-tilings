import FiniteDefects.D4DefectArmRooms

/-! # Three independent arms over one literal defect placement -/

namespace FiniteDefects

structure D4ArmTriple (m : ℕ) (defect : D4DefectPlacement m) where
  zero : D4ArmPath m .zero (defect.core .zero)
  one : D4ArmPath m .one (defect.core .one)
  two : D4ArmPath m .two (defect.core .two)

theorem d4DefectPathData_ext {m : ℕ}
    (left right : D4DefectPathData m)
    (hdefect : left.defect = right.defect)
    (hpaths : HEq left.paths right.paths) : left = right := by
  rcases left with ⟨leftDefect, leftPaths, leftSpec⟩
  rcases right with ⟨rightDefect, rightPaths, rightSpec⟩
  dsimp at hdefect hpaths
  subst rightDefect
  have hpathsEq : leftPaths = rightPaths := eq_of_heq hpaths
  subst rightPaths
  rfl

noncomputable def d4ArmTripleFintype {m : ℕ}
    (defect : D4DefectPlacement m) : Fintype (D4ArmTriple m defect) := by
  letI := d4ArmPathFintype .zero (defect.core .zero) (defect.arm_room .zero)
  letI := d4ArmPathFintype .one (defect.core .one) (defect.arm_room .one)
  letI := d4ArmPathFintype .two (defect.core .two) (defect.arm_room .two)
  exact Fintype.ofEquiv
    (D4ArmPath m .zero (defect.core .zero) ×
      D4ArmPath m .one (defect.core .one) ×
      D4ArmPath m .two (defect.core .two))
    { toFun := fun paths => ⟨paths.1, paths.2.1, paths.2.2⟩
      invFun := fun paths => (paths.zero, paths.one, paths.two)
      left_inv := by intro paths; cases paths; rfl
      right_inv := by intro paths; cases paths; rfl }

theorem card_d4ArmTriple {m : ℕ} (defect : D4DefectPlacement m) :
    @Fintype.card (D4ArmTriple m defect) (d4ArmTripleFintype defect) =
      ballotNumber
          ((defect.core .zero).u + 2 * (defect.core .zero).v)
          (defect.core .zero).v *
        ballotNumber
          ((defect.core .one).v + 2 * (defect.core .one).w)
          (defect.core .one).w *
        ballotNumber
          ((defect.core .two).w + 2 * (defect.core .two).u)
          (defect.core .two).u := by
  letI := d4ArmPathFintype .zero (defect.core .zero) (defect.arm_room .zero)
  letI := d4ArmPathFintype .one (defect.core .one) (defect.arm_room .one)
  letI := d4ArmPathFintype .two (defect.core .two) (defect.arm_room .two)
  letI := d4ArmTripleFintype defect
  rw [show @Fintype.card (D4ArmTriple m defect)
      (d4ArmTripleFintype defect) =
      Fintype.card (D4ArmPath m .zero (defect.core .zero) ×
        D4ArmPath m .one (defect.core .one) ×
        D4ArmPath m .two (defect.core .two)) by
    exact Fintype.card_congr
      { toFun := fun paths => (paths.zero, paths.one, paths.two)
        invFun := fun paths => ⟨paths.1, paths.2.1, paths.2.2⟩
        left_inv := by intro paths; cases paths; rfl
        right_inv := by intro paths; cases paths; rfl }]
  rw [Fintype.card_prod, Fintype.card_prod]
  rw [card_d4ArmPath_zero, card_d4ArmPath_one, card_d4ArmPath_two]
  simp [Nat.mul_assoc]

noncomputable def d4PathDataEquivSigmaArmTriple (m : ℕ) :
    D4DefectPathData m ≃ Σ defect : D4DefectPlacement m,
      D4ArmTriple m defect where
  toFun := fun data => ⟨data.defect,
    ⟨⟨data.paths .zero, data.path_spec .zero⟩,
      ⟨data.paths .one, data.path_spec .one⟩,
      ⟨data.paths .two, data.path_spec .two⟩⟩⟩
  invFun := fun data =>
    { defect := data.1
      paths := fun label => match label with
        | .zero => data.2.zero.1
        | .one => data.2.one.1
        | .two => data.2.two.1
      path_spec := fun label => by
        rcases label with _ | _ | _
        · exact data.2.zero.2
        · exact data.2.one.2
        · exact data.2.two.2 }
  left_inv := by
    intro data
    apply d4DefectPathData_ext
    · rfl
    · apply heq_of_eq
      funext label
      rcases label <;> rfl
  right_inv := by
    intro data
    rcases data with ⟨defect, paths⟩
    cases paths
    rfl

noncomputable def d4LiteralTilingEquivSigmaArmTriple (m : ℕ) :
    D4LiteralTiling m ≃ Σ defect : D4DefectPlacement m,
      D4ArmTriple m defect :=
  (d4LiteralTilingEquivPathData m).trans
    (d4PathDataEquivSigmaArmTriple m)

end FiniteDefects
