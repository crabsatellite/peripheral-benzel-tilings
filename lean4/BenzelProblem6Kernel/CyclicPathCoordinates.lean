import BenzelProblem6Kernel.PathVertexVisits

/-!
# Cyclic coordinate variants for the other two corner exclusions
-/

namespace BenzelProblem6Kernel

theorem labelTwo_edge_v_mono {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .two) :
    edge.source.v ≤ edge.target.v := by
  have hanchor := literalDirectedEdge_anchor_step edge
  rcases labelTwo_edge_step_cases edge hlabel with hA | hB
  · rw [hA] at hanchor
    have hcoords := stepA_simplex_coordinates edge.source edge.target hanchor
    omega
  · rw [hB] at hanchor
    have hcoords := stepB_simplex_coordinates edge.source edge.target hanchor
    omega

theorem labelTwo_edge_stepA_of_v_eq {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .two)
    (hv : edge.source.v = edge.target.v) :
    edge.boneClass.step = stepA := by
  rcases labelTwo_edge_step_cases edge hlabel with hA | hB
  · exact hA
  · have hanchor := literalDirectedEdge_anchor_step edge
    rw [hB] at hanchor
    have hcoords := stepB_simplex_coordinates edge.source edge.target hanchor
    omega

theorem LiteralEdgePath.labelTwo_v_mono
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .two) :
    first.source.v ≤ last.target.v := by
  induction path with
  | single hedge => exact labelTwo_edge_v_mono first hlabel
  | @snoc previous next path hnext hmeet hsame ih =>
      have hp := ih (hsame.trans hlabel)
      have hn := labelTwo_edge_v_mono next hlabel
      rw [hmeet] at hp
      exact hp.trans hn

theorem LiteralEdgePath.labelTwo_all_steps_A
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .two)
    (hend : last.target.v = 0) :
    path.AllEdges (fun edge => edge.boneClass.step = stepA) := by
  induction path with
  | single hedge =>
      exact LiteralEdgePath.AllEdges.single _ hedge
        (labelTwo_edge_stepA_of_v_eq first hlabel (by
          have := labelTwo_edge_v_mono first hlabel
          omega))
  | @snoc previous next path hnext hmeet hsame ih =>
      have hnextMono := labelTwo_edge_v_mono next hlabel
      have hnextSource : next.source.v = 0 := by omega
      have hpreviousEnd : previous.target.v = 0 := by
        rw [hmeet]
        exact hnextSource
      have hpreviousLabel := hsame.trans hlabel
      exact LiteralEdgePath.AllEdges.snoc (ih hpreviousLabel hpreviousEnd)
        hnext hmeet hsame
        (labelTwo_edge_stepA_of_v_eq next hlabel (by omega))

theorem labelZero_edge_step_cases {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .zero) :
    edge.boneClass.step = stepA ∨ edge.boneClass.step = stepC := by
  have hallowed := literalDirectedEdge_allowed edge
  rw [hlabel] at hallowed
  exact hallowed

theorem labelZero_edge_w_mono {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .zero) :
    edge.source.w ≤ edge.target.w := by
  have hanchor := literalDirectedEdge_anchor_step edge
  rcases labelZero_edge_step_cases edge hlabel with hA | hC
  · rw [hA] at hanchor
    have hcoords := stepA_simplex_coordinates edge.source edge.target hanchor
    omega
  · rw [hC] at hanchor
    have hcoords := stepC_simplex_coordinates edge.source edge.target hanchor
    omega

theorem labelZero_edge_stepC_of_w_eq {m : ℕ} (edge : LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .zero)
    (hw : edge.source.w = edge.target.w) :
    edge.boneClass.step = stepC := by
  rcases labelZero_edge_step_cases edge hlabel with hA | hC
  · have hanchor := literalDirectedEdge_anchor_step edge
    rw [hA] at hanchor
    have hcoords := stepA_simplex_coordinates edge.source edge.target hanchor
    omega
  · exact hC

theorem LiteralEdgePath.labelZero_w_mono
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .zero) :
    first.source.w ≤ last.target.w := by
  induction path with
  | single hedge => exact labelZero_edge_w_mono first hlabel
  | @snoc previous next path hnext hmeet hsame ih =>
      have hp := ih (hsame.trans hlabel)
      have hn := labelZero_edge_w_mono next hlabel
      rw [hmeet] at hp
      exact hp.trans hn

theorem LiteralEdgePath.labelZero_all_steps_C
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .zero)
    (hend : last.target.w = 0) :
    path.AllEdges (fun edge => edge.boneClass.step = stepC) := by
  induction path with
  | single hedge =>
      exact LiteralEdgePath.AllEdges.single _ hedge
        (labelZero_edge_stepC_of_w_eq first hlabel (by
          have := labelZero_edge_w_mono first hlabel
          omega))
  | @snoc previous next path hnext hmeet hsame ih =>
      have hnextMono := labelZero_edge_w_mono next hlabel
      have hnextSource : next.source.w = 0 := by omega
      have hpreviousEnd : previous.target.w = 0 := by
        rw [hmeet]
        exact hnextSource
      have hpreviousLabel := hsame.trans hlabel
      exact LiteralEdgePath.AllEdges.snoc (ih hpreviousLabel hpreviousEnd)
        hnext hmeet hsame
        (labelZero_edge_stepC_of_w_eq next hlabel (by omega))

theorem LiteralEdgePath.exists_labelZero_last_C_target_v_zero
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .zero)
    (hstartPos : 0 < first.source.v)
    (hend : last.target.v = 0) :
    ∃ pivot ∈ literalDirectedEdges hstone tiling,
      pivot.boneClass.label = .zero ∧
        pivot.boneClass.step = stepC ∧ pivot.target.v = 0 := by
  induction path with
  | single hedge =>
      rcases labelZero_edge_step_cases first hlabel with hA | hC
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hA] at hanchor
        have hcoords := stepA_simplex_coordinates first.source first.target hanchor
        omega
      · exact ⟨first, hedge, hlabel, hC, hend⟩
  | @snoc previous next path hnext hmeet hsame ih =>
      rcases labelZero_edge_step_cases next hlabel with hA | hC
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hA] at hanchor
        have hcoords := stepA_simplex_coordinates next.source next.target hanchor
        have hprevEnd : previous.target.v = 0 := by rw [hmeet]; omega
        exact ih (hsame.trans hlabel) hprevEnd
      · exact ⟨next, hnext, hlabel, hC, hend⟩

theorem labelZero_C_target_u_pos {m : ℕ} (edge : LiteralDirectedEdge m)
    (hC : edge.boneClass.step = stepC) : 0 < edge.target.u := by
  have hanchor := literalDirectedEdge_anchor_step edge
  rw [hC] at hanchor
  have hcoords := stepC_simplex_coordinates edge.source edge.target hanchor
  omega

theorem LiteralEdgePath.exists_labelOne_last_B_target_w_zero
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hlabel : last.boneClass.label = .one)
    (hstartPos : 0 < first.source.w)
    (hend : last.target.w = 0) :
    ∃ pivot ∈ literalDirectedEdges hstone tiling,
      pivot.boneClass.label = .one ∧
        pivot.boneClass.step = stepB ∧ pivot.target.w = 0 := by
  induction path with
  | single hedge =>
      rcases labelOne_edge_step_cases first hlabel with hB | hC
      · exact ⟨first, hedge, hlabel, hB, hend⟩
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hC] at hanchor
        have hcoords := stepC_simplex_coordinates first.source first.target hanchor
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      rcases labelOne_edge_step_cases next hlabel with hB | hC
      · exact ⟨next, hnext, hlabel, hB, hend⟩
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hC] at hanchor
        have hcoords := stepC_simplex_coordinates next.source next.target hanchor
        have hprevEnd : previous.target.w = 0 := by rw [hmeet]; omega
        exact ih (hsame.trans hlabel) hprevEnd

theorem labelOne_B_target_v_pos {m : ℕ} (edge : LiteralDirectedEdge m)
    (hB : edge.boneClass.step = stepB) : 0 < edge.target.v := by
  have hanchor := literalDirectedEdge_anchor_step edge
  rw [hB] at hanchor
  have hcoords := stepB_simplex_coordinates edge.source edge.target hanchor
  omega

end BenzelProblem6Kernel
