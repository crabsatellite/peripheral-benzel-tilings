import BenzelProblem6Kernel.TilingComplexEdgeLength

/-! # Source and target vertex sets of continuous closed edge paths -/

namespace BenzelProblem6Kernel

def edgeTargetFinset (edges : List LabeledHexEdge) : Finset HexVertex :=
  (edges.map LabeledHexEdge.target).toFinset

theorem ContinuousLabeledEdgePath.source_finish_eq_start_target
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish) :
    edgeSourceFinset edges ∪ {finish} =
      {start} ∪ edgeTargetFinset edges := by
  induction path with
  | nil => simp [edgeSourceFinset, edgeTargetFinset]
  | @cons edge rest target tail ih =>
      simp only [edgeSourceFinset, edgeTargetFinset,
        List.map_cons, List.toFinset_cons]
      change (insert edge.source (edgeSourceFinset rest)) ∪ {target} =
        {edge.source} ∪ insert edge.target (edgeTargetFinset rest)
      rw [show insert edge.source (edgeSourceFinset rest) =
          {edge.source} ∪ edgeSourceFinset rest by rfl,
        show insert edge.target (edgeTargetFinset rest) =
          {edge.target} ∪ edgeTargetFinset rest by rfl,
        Finset.union_assoc, ih]

theorem edgeSourceFinset_reverseReoriented
    (edges : List LabeledHexEdge) :
    edgeSourceFinset (reverseReorientedEdges edges) =
      edgeTargetFinset edges := by
  ext vertex
  simp [edgeSourceFinset, edgeTargetFinset,
    reverseReorientedEdges, reverseLabeledHexEdge]

theorem ContinuousLabeledEdgePath.start_mem_source_of_ne_nil
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hne : edges ≠ []) : start ∈ edgeSourceFinset edges := by
  cases edges with
  | nil => exact (hne rfl).elim
  | cons edge rest =>
      cases path
      simp [edgeSourceFinset]

theorem ContinuousLabeledEdgePath.finish_mem_target_of_ne_nil
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hne : edges ≠ []) : finish ∈ edgeTargetFinset edges := by
  have hsource := path.reverse.start_mem_source_of_ne_nil (by
    simp [reverseReorientedEdges, hne])
  change finish ∈ edgeSourceFinset
    (reverseReorientedEdges edges) at hsource
  rwa [edgeSourceFinset_reverseReoriented] at hsource

theorem ContinuousLabeledEdgePath.closed_source_eq_target
    {root : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath root edges root) :
    edgeSourceFinset edges = edgeTargetFinset edges := by
  cases edges with
  | nil => rfl
  | cons edge rest =>
      have hrootSource : root ∈ edgeSourceFinset (edge :: rest) := by
        cases path with
        | cons edge tail =>
            simp [edgeSourceFinset]
      have hrootTarget : root ∈ edgeTargetFinset (edge :: rest) :=
        path.finish_mem_target_of_ne_nil (by simp)
      have heq := path.source_finish_eq_start_target
      ext vertex
      have hmem := Finset.ext_iff.mp heq vertex
      simp only [Finset.mem_union, Finset.mem_singleton] at hmem
      by_cases hvertex : vertex = root
      · subst vertex
        exact iff_of_true hrootSource hrootTarget
      · simpa [hvertex] using hmem

theorem RootedAlternatingBoundary.reverse_source_eq_source
    (boundary : RootedAlternatingBoundary) :
    edgeSourceFinset (reverseReorientedEdges boundary.edges) =
      edgeSourceFinset boundary.edges := by
  rw [edgeSourceFinset_reverseReoriented,
    ← boundary.continuous.closed_source_eq_target]

theorem placement_reverse_source_eq_source {m : ℕ}
    (placement : LiteralPlacement m) :
    edgeSourceFinset
        (reverseReorientedEdges (literalPlacementBoundary placement)) =
      placementBoundaryVertexFinset placement := by
  let boundary := literalPlacementRootedBoundary placement
  exact boundary.reverse_source_eq_source

end BenzelProblem6Kernel
