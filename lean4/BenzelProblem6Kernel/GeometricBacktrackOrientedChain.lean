import BenzelProblem6Kernel.PeripheralDirectedBoundary

/-! # Backtrack normalization preserves every directed-edge coefficient -/

namespace BenzelProblem6Kernel

theorem prependReducedEdge_same_chain
    (edge : LabeledHexEdge) (rest : List LabeledHexEdge) :
    SameOrientedBoundaryChain (edge :: rest)
      (prependReducedEdge edge rest) := by
  cases rest with
  | nil => exact SameOrientedBoundaryChain.refl _
  | cons next tail =>
      by_cases hreverse : reverseLabeledHexEdge edge = next
      · subst next
        simp only [prependReducedEdge, if_pos rfl]
        have hpair := reversePair_same_empty edge
        have htail := hpair.append (SameOrientedBoundaryChain.refl tail)
        simpa using htail
      · simp [prependReducedEdge, hreverse]
        exact SameOrientedBoundaryChain.refl _

theorem reduceGeometricBacktracks_same_chain
    (edges : List LabeledHexEdge) :
    SameOrientedBoundaryChain edges
      (reduceGeometricBacktracks edges) := by
  induction edges with
  | nil => exact SameOrientedBoundaryChain.refl _
  | cons edge rest ih =>
      exact ((SameOrientedBoundaryChain.refl [edge]).append ih).trans
        (prependReducedEdge_same_chain edge
          (reduceGeometricBacktracks rest))

end BenzelProblem6Kernel
