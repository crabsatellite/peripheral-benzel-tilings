import BenzelProblem6Kernel.GeometricBoundaryPeeling

/-!
# Kernel-checked linear backtrack normalization

This is ordinary free reduction on literal oriented honeycomb edges.  Only an
edge immediately followed by the same edge in reverse may disappear.  No
cyclic endpoint cancellation, commutation, or edge-key-only cancellation is
performed.
-/

namespace BenzelProblem6Kernel

def prependReducedEdge (edge : LabeledHexEdge) :
    List LabeledHexEdge → List LabeledHexEdge
  | [] => [edge]
  | next :: rest =>
      if reverseLabeledHexEdge edge = next then rest
      else edge :: next :: rest

def reduceGeometricBacktracks :
    List LabeledHexEdge → List LabeledHexEdge
  | [] => []
  | edge :: rest =>
      prependReducedEdge edge (reduceGeometricBacktracks rest)

theorem reverseLabeledHexEdge_involutive (edge : LabeledHexEdge) :
    reverseLabeledHexEdge (reverseLabeledHexEdge edge) = edge := by
  cases edge
  rfl

theorem prependReducedEdge_word_equivalent
    (edge : LabeledHexEdge) (rest : List LabeledHexEdge) :
    InvolutiveWordEquivalent
      (edge.label :: labeledEdgeWord rest)
      (labeledEdgeWord (prependReducedEdge edge rest)) := by
  cases rest with
  | nil => exact Relation.EqvGen.refl _
  | cons next tail =>
      by_cases hreverse : reverseLabeledHexEdge edge = next
      · have hlabel : edge.label = next.label := by
          rw [← hreverse]
          rfl
        simp only [prependReducedEdge, hreverse, if_pos,
          labeledEdgeWord, List.map_cons]
        rw [hlabel]
        exact Relation.EqvGen.rel _ _
          (InvolutionCancelStep.cancel [] (labeledEdgeWord tail) next.label)
      · simp only [prependReducedEdge, hreverse, if_neg,
          labeledEdgeWord, List.map_cons]
        exact Relation.EqvGen.refl _

theorem reduceGeometricBacktracks_word_equivalent
    (edges : List LabeledHexEdge) :
    InvolutiveWordEquivalent (labeledEdgeWord edges)
      (labeledEdgeWord (reduceGeometricBacktracks edges)) := by
  induction edges with
  | nil => exact Relation.EqvGen.refl _
  | cons edge rest ih =>
      have hcontext : InvolutiveWordEquivalent
          (edge.label :: labeledEdgeWord rest)
          (edge.label ::
            labeledEdgeWord (reduceGeometricBacktracks rest)) := by
        simpa [labeledEdgeWord] using
          involutiveWordEquivalent_append_left [edge.label] ih
      have hprepend := prependReducedEdge_word_equivalent edge
        (reduceGeometricBacktracks rest)
      exact Relation.EqvGen.trans _ _ _ hcontext (by
        simpa [labeledEdgeWord, reduceGeometricBacktracks] using hprepend)

end BenzelProblem6Kernel
