import BenzelProblem6Kernel.DownBenzelVertexTwo

/-! # Injectivity of the down-vertex parameter map -/

namespace BenzelProblem6Kernel

def downVertexParameterToAnchor (m : ℕ)
    (parameter : DownVertexParameter (m + 3)) :
    DownBenzelVertexAnchor m := by
  refine ⟨downVertexParameterAnchor parameter, ?_⟩
  rcases parameter with p | p
  · exact downZeroParameter_anchor_mem m p
  · rcases p with p | p
    · exact downOneParameter_anchor_mem m p
    · exact downTwoParameter_anchor_mem m p

theorem downZeroParameterAnchor_injective (t : ℕ) :
    Function.Injective
      (downZeroParameterAnchor : DownZeroParameter t → Cell) := by
  intro left right hanchor
  apply Subtype.ext
  apply simplexPoint_ext
  all_goals
    have hleft := left.1.sum_eq
    have hright := right.1.sum_eq
    simp [downZeroParameterAnchor, downZeroSimplexAnchor] at hanchor
    omega

theorem downOneParameterAnchor_injective (t : ℕ) :
    Function.Injective
      (downOneParameterAnchor : DownOneParameter t → Cell) := by
  intro left right hanchor
  apply Subtype.ext
  exact simplexAnchor_injective_at_total (t + 1) hanchor

theorem downTwoParameterAnchor_injective (t : ℕ) :
    Function.Injective
      (downTwoParameterAnchor : DownTwoParameter t → Cell) := by
  intro left right hanchor
  apply Subtype.ext
  apply simplexPoint_ext
  all_goals
    have hleft := left.1.sum_eq
    have hright := right.1.sum_eq
    simp [downTwoParameterAnchor, downTwoSimplexAnchor] at hanchor
    omega

theorem downZero_ne_downOne {t : ℕ}
    (left : DownZeroParameter t) (right : DownOneParameter t) :
    downZeroParameterAnchor left ≠ downOneParameterAnchor right := by
  intro hanchor
  have hleft := left.1.sum_eq
  have hright := right.1.sum_eq
  simp [downZeroParameterAnchor, downZeroSimplexAnchor,
    downOneParameterAnchor, downOneSimplexAnchor,
    simplexAnchor] at hanchor
  omega

theorem downZero_ne_downTwo {t : ℕ}
    (left : DownZeroParameter t) (right : DownTwoParameter t) :
    downZeroParameterAnchor left ≠ downTwoParameterAnchor right := by
  intro hanchor
  have hleft := left.1.sum_eq
  have hright := right.1.sum_eq
  simp [downZeroParameterAnchor, downZeroSimplexAnchor,
    downTwoParameterAnchor, downTwoSimplexAnchor] at hanchor
  omega

theorem downOne_ne_downTwo {t : ℕ}
    (left : DownOneParameter t) (right : DownTwoParameter t) :
    downOneParameterAnchor left ≠ downTwoParameterAnchor right := by
  intro hanchor
  have hleft := left.1.sum_eq
  have hright := right.1.sum_eq
  simp [downOneParameterAnchor, downOneSimplexAnchor,
    downTwoParameterAnchor, downTwoSimplexAnchor,
    simplexAnchor] at hanchor
  omega

theorem downVertexParameterAnchor_injective (m : ℕ) :
    Function.Injective
      (downVertexParameterAnchor : DownVertexParameter (m + 3) → Cell) := by
  intro left right hanchor
  cases left with
  | inl p0 =>
      cases right with
      | inl q0 =>
          exact congrArg Sum.inl
            (downZeroParameterAnchor_injective (m + 3) hanchor)
      | inr q =>
          cases q with
          | inl q1 => exact (downZero_ne_downOne p0 q1 hanchor).elim
          | inr q2 => exact (downZero_ne_downTwo p0 q2 hanchor).elim
  | inr p =>
      cases p with
      | inl p1 =>
          cases right with
          | inl q0 => exact (downZero_ne_downOne q0 p1 hanchor.symm).elim
          | inr q =>
              cases q with
              | inl q1 =>
                  exact congrArg (fun item => Sum.inr (Sum.inl item))
                    (downOneParameterAnchor_injective (m + 3) hanchor)
              | inr q2 => exact (downOne_ne_downTwo p1 q2 hanchor).elim
      | inr p2 =>
          cases right with
          | inl q0 => exact (downZero_ne_downTwo q0 p2 hanchor.symm).elim
          | inr q =>
              cases q with
              | inl q1 => exact (downOne_ne_downTwo q1 p2 hanchor.symm).elim
              | inr q2 =>
                  exact congrArg (fun item => Sum.inr (Sum.inr item))
                    (downTwoParameterAnchor_injective (m + 3) hanchor)

theorem downVertexParameterToAnchor_injective (m : ℕ) :
    Function.Injective (downVertexParameterToAnchor m) := by
  intro left right h
  apply downVertexParameterAnchor_injective m
  exact congrArg Subtype.val h

end BenzelProblem6Kernel
