import BenzelProblem6Kernel.UpBenzelVertexTwo

/-! # Injectivity of the up-vertex parameter map -/

namespace BenzelProblem6Kernel

def upVertexParameterToAnchor (m : ℕ)
    (parameter : UpVertexParameter (m + 3)) :
    UpBenzelVertexAnchor m := by
  refine ⟨upVertexParameterAnchor parameter, ?_⟩
  rcases parameter with p | p
  · exact upZeroParameter_anchor_mem m p
  · rcases p with p | p
    · exact upOneParameter_anchor_mem m p
    · exact upTwoParameter_anchor_mem m p

theorem simplexAnchor_ne_succ_total {t : ℕ}
    (left : SimplexPoint t) (right : SimplexPoint (t + 1)) :
    simplexAnchor left ≠ simplexAnchor right := by
  intro hanchor
  have hleft := left.sum_eq
  have hright := right.sum_eq
  simp [simplexAnchor] at hanchor
  omega

theorem simplexAnchor_ne_add_two_total {t : ℕ}
    (left : SimplexPoint t) (right : SimplexPoint (t + 2)) :
    simplexAnchor left ≠ simplexAnchor right := by
  intro hanchor
  have hleft := left.sum_eq
  have hright := right.sum_eq
  simp [simplexAnchor] at hanchor
  omega

theorem upVertexParameterAnchor_injective (m : ℕ) :
    Function.Injective
      (upVertexParameterAnchor : UpVertexParameter (m + 3) → Cell) := by
  intro left right hanchor
  cases left with
  | inl p0 =>
      cases right with
      | inl q0 =>
          exact congrArg Sum.inl
            (simplexAnchor_injective_at_total (m + 3) hanchor)
      | inr q =>
          cases q with
          | inl q1 =>
              exact (simplexAnchor_ne_succ_total p0 q1.1 hanchor).elim
          | inr q2 =>
              exact (simplexAnchor_ne_add_two_total p0 q2.1 hanchor).elim
  | inr p =>
      cases p with
      | inl p1 =>
          cases right with
          | inl q0 =>
              exact (simplexAnchor_ne_succ_total q0 p1.1 hanchor.symm).elim
          | inr q =>
              cases q with
              | inl q1 =>
                  have hp : p1.1 = q1.1 :=
                    simplexAnchor_injective_at_total (m + 3 + 1) hanchor
                  exact congrArg (fun item => Sum.inr (Sum.inl item))
                    (Subtype.ext hp)
              | inr q2 =>
                  exact (simplexAnchor_ne_succ_total p1.1 q2.1 hanchor).elim
      | inr p2 =>
          cases right with
          | inl q0 =>
              exact (simplexAnchor_ne_add_two_total q0 p2.1 hanchor.symm).elim
          | inr q =>
              cases q with
              | inl q1 =>
                  exact (simplexAnchor_ne_succ_total q1.1 p2.1 hanchor.symm).elim
              | inr q2 =>
                  have hp : p2.1 = q2.1 :=
                    simplexAnchor_injective_at_total (m + 3 + 2) hanchor
                  exact congrArg (fun item => Sum.inr (Sum.inr item))
                    (Subtype.ext hp)

theorem upVertexParameterToAnchor_injective (m : ℕ) :
    Function.Injective (upVertexParameterToAnchor m) := by
  intro left right h
  apply upVertexParameterAnchor_injective m
  exact congrArg Subtype.val h

end BenzelProblem6Kernel
