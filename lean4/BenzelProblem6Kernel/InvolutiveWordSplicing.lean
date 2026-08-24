import BenzelProblem6Kernel.LiteralPlacementFactor

/-!
# Splicing a tile face into a boundary walk

This is the noncommutative core of the Conway--Lagarias planar induction.  If
an oriented region boundary and an oriented tile boundary share their leading
edge, deleting the tile replaces that edge by the reverse of the rest of the
tile boundary.  The old word is exactly equivalent to the tile conjugate
followed by this spliced boundary.
-/

namespace BenzelProblem6Kernel

theorem involutiveWordEquivalent_append_context
    (leftContext rightContext : List ShadowLabel)
    {left right : List ShadowLabel}
    (heq : InvolutiveWordEquivalent left right) :
    InvolutiveWordEquivalent
      (leftContext ++ left ++ rightContext)
      (leftContext ++ right ++ rightContext) := by
  exact involutiveWordEquivalent_append_right
    (involutiveWordEquivalent_append_left leftContext heq) rightContext

theorem word_append_reverse_equivalent_empty (word : List ShadowLabel) :
    InvolutiveWordEquivalent (word ++ word.reverse) [] := by
  induction word with
  | nil => exact Relation.EqvGen.refl _
  | cons label rest ih =>
      have hinner : InvolutiveWordEquivalent
          ([label] ++ (rest ++ rest.reverse) ++ [label])
          ([label] ++ [] ++ [label]) :=
        involutiveWordEquivalent_append_context [label] [label] ih
      have hpair : InvolutiveWordEquivalent [label, label] [] := by
        exact Relation.EqvGen.rel _ _
          (InvolutionCancelStep.cancel [] [] label)
      have hshape :
          label :: rest ++ (label :: rest).reverse =
            [label] ++ (rest ++ rest.reverse) ++ [label] := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hshape]
      exact Relation.EqvGen.trans _ _ _ hinner (by simpa using hpair)

theorem reverse_append_word_equivalent_empty (word : List ShadowLabel) :
    InvolutiveWordEquivalent (word.reverse ++ word) [] := by
  simpa using word_append_reverse_equivalent_empty word.reverse

theorem involutiveWordEquivalent_erase_roundtrip
    (before middle after : List ShadowLabel) :
    InvolutiveWordEquivalent
      (before ++ middle.reverse ++ middle ++ after)
      (before ++ after) := by
  have hcancel := reverse_append_word_equivalent_empty middle
  simpa [List.append_assoc] using
    involutiveWordEquivalent_append_context before after hcancel

theorem involutiveWordEquivalent_erase_return
    (before middle after : List ShadowLabel) :
    InvolutiveWordEquivalent
      (before ++ middle ++ middle.reverse ++ after)
      (before ++ after) := by
  have hcancel := word_append_reverse_equivalent_empty middle
  simpa [List.append_assoc] using
    involutiveWordEquivalent_append_context before after hcancel

def spliceTileRestIntoBoundary
    (before tileRest after : List ShadowLabel) : List ShadowLabel :=
  before ++ tileRest.reverse ++ after

theorem factorWord_append_splice_equivalent_boundary
    (before : List ShadowLabel) (label : ShadowLabel)
    (tileRest after : List ShadowLabel) :
    InvolutiveWordEquivalent
      (shadowConjugate before (label :: tileRest) ++
        spliceTileRestIntoBoundary before tileRest after)
      (before ++ label :: after) := by
  let afterPathCancellation :=
    before ++ label :: tileRest ++ tileRest.reverse ++ after
  have hpath : InvolutiveWordEquivalent
      (shadowConjugate before (label :: tileRest) ++
        spliceTileRestIntoBoundary before tileRest after)
      afterPathCancellation := by
    have hcancel := reverse_append_word_equivalent_empty before
    simpa [shadowConjugate, spliceTileRestIntoBoundary,
      afterPathCancellation, List.append_assoc] using
        involutiveWordEquivalent_append_context
          (before ++ label :: tileRest)
          (tileRest.reverse ++ after) hcancel
  have htile : InvolutiveWordEquivalent afterPathCancellation
      (before ++ label :: after) := by
    have hcancel := word_append_reverse_equivalent_empty tileRest
    simpa [afterPathCancellation, List.append_assoc] using
      involutiveWordEquivalent_append_context
        (before ++ [label]) after hcancel
  exact Relation.EqvGen.trans _ _ _ hpath htile

theorem boundary_equivalent_factorWord_append_splice
    (before : List ShadowLabel) (label : ShadowLabel)
    (tileRest after : List ShadowLabel) :
    InvolutiveWordEquivalent (before ++ label :: after)
      (shadowConjugate before (label :: tileRest) ++
        spliceTileRestIntoBoundary before tileRest after) := by
  exact Relation.EqvGen.symm _ _
    (factorWord_append_splice_equivalent_boundary
      before label tileRest after)

end BenzelProblem6Kernel
