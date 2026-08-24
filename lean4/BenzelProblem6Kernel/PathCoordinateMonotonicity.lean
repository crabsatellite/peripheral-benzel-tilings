import BenzelProblem6Kernel.LiteralEdgePath

/-!
# Coordinate monotonicity along fixed-label literal paths
-/

namespace BenzelProblem6Kernel

theorem labelOne_edge_step_cases {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .one) :
    edge.boneClass.step = stepB ∨ edge.boneClass.step = stepC := by
  have hallowed := literalDirectedEdge_allowed edge
  rw [hlabel] at hallowed
  exact hallowed

theorem labelOne_edge_u_mono {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .one) :
    edge.source.u ≤ edge.target.u := by
  have hanchor := literalDirectedEdge_anchor_step edge
  rcases labelOne_edge_step_cases edge hlabel with hB | hC
  · rw [hB] at hanchor
    have hcoords := stepB_simplex_coordinates edge.source edge.target hanchor
    omega
  · rw [hC] at hanchor
    have hcoords := stepC_simplex_coordinates edge.source edge.target hanchor
    omega

theorem labelOne_edge_stepB_of_u_eq {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .one)
    (hu : edge.source.u = edge.target.u) :
    edge.boneClass.step = stepB := by
  rcases labelOne_edge_step_cases edge hlabel with hB | hC
  · exact hB
  · have hanchor := literalDirectedEdge_anchor_step edge
    rw [hC] at hanchor
    have hcoords := stepC_simplex_coordinates edge.source edge.target hanchor
    omega

theorem LiteralEdgePath.labelOne_u_mono
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .one) :
    first.source.u ≤ last.target.u := by
  induction path with
  | single hedge =>
      exact labelOne_edge_u_mono first hlabel
  | @snoc previous next path hnext hmeet hsame ih =>
      have hpreviousLabel : previous.boneClass.label = .one := hsame.trans hlabel
      have hp := ih hpreviousLabel
      have hn := labelOne_edge_u_mono next hlabel
      rw [hmeet] at hp
      exact hp.trans hn

theorem LiteralEdgePath.labelOne_last_stepB_of_zero_endpoints
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .one)
    (hend : last.target.u = 0) :
    last.boneClass.step = stepB := by
  have hmono := path.labelOne_u_mono hlabel
  have hlastMono := labelOne_edge_u_mono last hlabel
  have hlastSource : last.source.u = 0 := by omega
  exact labelOne_edge_stepB_of_u_eq last hlabel (by omega)

inductive LiteralEdgePath.AllEdges
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (predicate : LiteralDirectedEdge m → Prop) :
    {first last : LiteralDirectedEdge m} →
      LiteralEdgePath hstone tiling first last → Prop
  | single (edge : LiteralDirectedEdge m)
      (hedge : edge ∈ literalDirectedEdges hstone tiling)
      (hp : predicate edge) :
      AllEdges predicate (LiteralEdgePath.single edge hedge)
  | snoc {first last next : LiteralDirectedEdge m}
      {path : LiteralEdgePath hstone tiling first last}
      (hall : AllEdges predicate path)
      (hnext : next ∈ literalDirectedEdges hstone tiling)
      (hmeet : last.target = next.source)
      (hlabel : last.boneClass.label = next.boneClass.label)
      (hp : predicate next) :
      AllEdges predicate (LiteralEdgePath.snoc path hnext hmeet hlabel)

theorem LiteralEdgePath.labelOne_all_steps_B
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .one)
    (hend : last.target.u = 0) :
    path.AllEdges (fun edge => edge.boneClass.step = stepB) := by
  induction path with
  | single hedge =>
      exact LiteralEdgePath.AllEdges.single _ hedge
        (labelOne_edge_stepB_of_u_eq first hlabel (by
          have := labelOne_edge_u_mono first hlabel
          omega))
  | @snoc previous next path hnext hmeet hsame ih =>
      have hnextMono := labelOne_edge_u_mono next hlabel
      have hnextSource : next.source.u = 0 := by omega
      have hpreviousEnd : previous.target.u = 0 := by
        rw [hmeet]
        exact hnextSource
      have hpreviousLabel : previous.boneClass.label = .one := hsame.trans hlabel
      exact LiteralEdgePath.AllEdges.snoc (ih hpreviousLabel hpreviousEnd)
        hnext hmeet hsame
        (labelOne_edge_stepB_of_u_eq next hlabel (by omega))

theorem labelTwo_edge_step_cases {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .two) :
    edge.boneClass.step = stepA ∨ edge.boneClass.step = stepB := by
  have hallowed := literalDirectedEdge_allowed edge
  rw [hlabel] at hallowed
  exact hallowed

theorem LiteralEdgePath.exists_labelTwo_last_A_target_u_zero
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .two)
    (hstartPos : 0 < first.source.u)
    (hend : last.target.u = 0) :
    ∃ pivot ∈ literalDirectedEdges hstone tiling,
      pivot.boneClass.label = .two ∧
        pivot.boneClass.step = stepA ∧ pivot.target.u = 0 := by
  induction path with
  | single hedge =>
      rcases labelTwo_edge_step_cases first hlabel with hA | hB
      · exact ⟨first, hedge, hlabel, hA, hend⟩
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hB] at hanchor
        have hcoords := stepB_simplex_coordinates first.source first.target hanchor
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      rcases labelTwo_edge_step_cases next hlabel with hA | hB
      · exact ⟨next, hnext, hlabel, hA, hend⟩
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hB] at hanchor
        have hcoords := stepB_simplex_coordinates next.source next.target hanchor
        have hprevEnd : previous.target.u = 0 := by
          rw [hmeet]
          omega
        have hprevLabel : previous.boneClass.label = .two := hsame.trans hlabel
        exact ih hprevLabel hprevEnd

theorem labelTwo_A_target_w_pos {m : ℕ} (edge : LiteralDirectedEdge m)
    (hA : edge.boneClass.step = stepA) : 0 < edge.target.w := by
  have hanchor := literalDirectedEdge_anchor_step edge
  rw [hA] at hanchor
  have hcoords := stepA_simplex_coordinates edge.source edge.target hanchor
  omega

end BenzelProblem6Kernel
