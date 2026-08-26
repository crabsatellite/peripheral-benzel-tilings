import D4KernelOnly.D4BoundaryNodup
import BenzelProblem6Kernel.GeometricBacktrackOrientedChain

/-! # Backtrack-reduced rooted boundary for the terminal-tree argument -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 800000

theorem continuousLabeledEdgePath_nil_eq
    {start finish : HexVertex}
    (path : ContinuousLabeledEdgePath start [] finish) : start = finish := by
  cases path
  rfl

theorem continuousLabeledEdgePath_cons_source
    {start finish : HexVertex} {edge : LabeledHexEdge}
    {rest : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start (edge :: rest) finish) :
    start = edge.source := by
  cases path
  rfl

theorem continuousLabeledEdgePath_cons_tail
    {start finish : HexVertex} {edge : LabeledHexEdge}
    {rest : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start (edge :: rest) finish) :
    ContinuousLabeledEdgePath edge.target rest finish := by
  cases path
  assumption

theorem prependReducedEdge_continuous
    {finish : HexVertex} (edge : LabeledHexEdge)
    (rest : List LabeledHexEdge)
    (hrest : ContinuousLabeledEdgePath edge.target rest finish) :
    ContinuousLabeledEdgePath edge.source
      (prependReducedEdge edge rest) finish := by
  by_cases hnil : rest = []
  · subst rest
    have hfinish := continuousLabeledEdgePath_nil_eq hrest
    subst finish
    exact .cons edge (.nil _)
  · obtain ⟨next, tail, hrestEq⟩ := List.exists_cons_of_ne_nil hnil
    subst rest
    have hsource := continuousLabeledEdgePath_cons_source hrest
    have htail := continuousLabeledEdgePath_cons_tail hrest
    by_cases hreverse : reverseLabeledHexEdge edge = next
    · have htarget : next.target = edge.source := by
        rw [← hreverse]
        rfl
      simp only [prependReducedEdge, hreverse, if_pos]
      rw [htarget] at htail
      exact htail
    · simp only [prependReducedEdge, hreverse, if_neg]
      exact .cons edge hrest

theorem reduceGeometricBacktracks_continuous
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish) :
    ContinuousLabeledEdgePath start
      (reduceGeometricBacktracks edges) finish := by
  induction path with
  | nil => exact .nil _
  | cons edge tail ih =>
      exact prependReducedEdge_continuous edge _ ih

theorem prependReducedEdge_sublist (edge : LabeledHexEdge)
    (rest : List LabeledHexEdge) :
    List.Sublist (prependReducedEdge edge rest) (edge :: rest) := by
  cases rest with
  | nil => exact List.Sublist.refl _
  | cons next tail =>
      by_cases hreverse : reverseLabeledHexEdge edge = next
      · simp only [prependReducedEdge, hreverse, if_pos]
        exact (tail.sublist_cons_self next).trans
          ((next :: tail).sublist_cons_self edge)
      · simp only [prependReducedEdge, hreverse, if_neg]
        exact List.Sublist.refl _

theorem reduceGeometricBacktracks_sublist (edges : List LabeledHexEdge) :
    List.Sublist (reduceGeometricBacktracks edges) edges := by
  induction edges with
  | nil => exact List.Sublist.refl _
  | cons edge rest ih =>
      exact (prependReducedEdge_sublist edge
        (reduceGeometricBacktracks rest)).trans (ih.cons_cons edge)

def d4ReducedBoundaryWalk (m : ℕ) : List LabeledHexEdge :=
  reduceGeometricBacktracks (d4LiteralBoundaryWalk m)

theorem d4ReducedBoundary_continuous (m : ℕ) :
    ContinuousLabeledEdgePath (d4LiteralBoundaryRoot m)
      (d4ReducedBoundaryWalk m) (d4LiteralBoundaryRoot m) :=
  reduceGeometricBacktracks_continuous (d4LiteralBoundary_continuous m)

theorem d4ReducedBoundary_edges_alternate (m : ℕ) :
    ∀ edge ∈ d4ReducedBoundaryWalk m,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  exact d4LiteralBoundaryWalk_edges_alternate m edge
    ((reduceGeometricBacktracks_sublist _).subset hedge)

theorem d4ReducedBoundary_nodup (m : ℕ) :
    (d4ReducedBoundaryWalk m).Nodup :=
  (d4LiteralBoundaryWalk_nodup m).sublist
    (reduceGeometricBacktracks_sublist _)

def d4ReducedRootedBoundary (m : ℕ) : RootedAlternatingBoundary where
  edges := d4ReducedBoundaryWalk m
  root := d4LiteralBoundaryRoot m
  continuous := d4ReducedBoundary_continuous m
  root_classZero := d4LiteralBoundaryRoot_classZero m
  alternates := d4ReducedBoundary_edges_alternate m

theorem d4ReducedBoundaryCoefficientInvariant {m : ℕ}
    (tiling : D4LiteralTiling m) :
    RightmostBoundaryCoefficientInvariant
      (d4ReducedBoundaryWalk m) (d4ShadowPlacementFinset tiling) := by
  intro cell
  exact ((reduceGeometricBacktracks_same_chain
    (d4LiteralBoundaryWalk m)) (cellBoundaryEdgeAt cell .side₅)).symm.trans
      (d4InitialRightmostBoundaryCoefficientInvariant tiling cell)

noncomputable def d4ReducedRightmostSkeleton {m : ℕ}
    (tiling : D4LiteralTiling m) :
    RightmostPeelingSkeleton m
      (d4ReducedRootedBoundary m) (d4ShadowPlacementFinset tiling) :=
  buildD4RightmostPeelingSkeleton tiling
    (d4ReducedRootedBoundary m) (d4ShadowPlacementFinset tiling)
    (fun _ h => h) (d4ReducedBoundaryCoefficientInvariant tiling)

noncomputable def d4ReducedRightmostTerminal {m : ℕ}
    (tiling : D4LiteralTiling m) : RootedAlternatingBoundary :=
  (d4ReducedRightmostSkeleton tiling).terminalRegion

end FiniteDefects
