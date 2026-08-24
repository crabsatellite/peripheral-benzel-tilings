import BenzelProblem6Kernel.PathCoordinateMonotonicity

/-!
# Vertices visited by a literal edge path
-/

namespace BenzelProblem6Kernel

inductive LiteralEdgePath.Visits
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m} :
    {first last : LiteralDirectedEdge m} →
      LiteralEdgePath hstone tiling first last →
      SimplexPoint (m + 3) → Prop
  | source {first last} (path : LiteralEdgePath hstone tiling first last) :
      Visits path first.source
  | singleTarget (edge : LiteralDirectedEdge m)
      (hedge : edge ∈ literalDirectedEdges hstone tiling) :
      Visits (LiteralEdgePath.single edge hedge) edge.target
  | ofPrefix {first last next} {path : LiteralEdgePath hstone tiling first last}
      (hnext : next ∈ literalDirectedEdges hstone tiling)
      (hmeet : last.target = next.source)
      (hlabel : last.boneClass.label = next.boneClass.label)
      {p : SimplexPoint (m + 3)} (hp : Visits path p) :
      Visits (LiteralEdgePath.snoc path hnext hmeet hlabel) p
  | lastTarget {first last next} (path : LiteralEdgePath hstone tiling first last)
      (hnext : next ∈ literalDirectedEdges hstone tiling)
      (hmeet : last.target = next.source)
      (hlabel : last.boneClass.label = next.boneClass.label) :
      Visits (LiteralEdgePath.snoc path hnext hmeet hlabel) next.target

theorem allB_path_visits_vertical_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    {path : LiteralEdgePath hstone tiling first last}
    (hall : path.AllEdges (fun edge => edge.boneClass.step = stepB))
    (hstartU : first.source.u = 0)
    (hstartV : first.source.v = 0)
    (hendU : last.target.u = 0)
    (k : ℕ) (hendV : last.target.v = k)
    (b : ℕ) (hb : b ≤ k) :
    ∃ p : SimplexPoint (m + 3),
      path.Visits p ∧ p.u = 0 ∧ p.v = b ∧ p.w = m + 3 - b := by
  induction hall generalizing k b with
  | single hedge hB =>
      have hanchor := literalDirectedEdge_anchor_step first
      rw [hB] at hanchor
      have hcoords := stepB_simplex_coordinates first.source first.target hanchor
      have hk : k = 1 := by omega
      subst k
      have hbCases : b = 0 ∨ b = 1 := by omega
      rcases hbCases with rfl | rfl
      · refine ⟨first.source, LiteralEdgePath.Visits.source
          (LiteralEdgePath.single first hedge), hstartU, hstartV, ?_⟩
        have hsum := first.source.sum_eq
        omega
      · refine ⟨first.target, LiteralEdgePath.Visits.singleTarget first hedge,
          hendU, by omega, ?_⟩
        have hsum := first.target.sum_eq
        omega
  | @snoc previous next path hall hnext hmeet hlabel hB ih =>
      have hanchor := literalDirectedEdge_anchor_step next
      rw [hB] at hanchor
      have hcoords := stepB_simplex_coordinates next.source next.target hanchor
      have hkpos : 0 < k := by omega
      by_cases hbk : b = k
      · subst b
        refine ⟨next.target,
          LiteralEdgePath.Visits.lastTarget path hnext hmeet hlabel,
          hendU, hendV, ?_⟩
        have hsum := next.target.sum_eq
        omega
      · have hbpred : b ≤ k - 1 := by omega
        have hprevU : previous.target.u = 0 := by
          rw [hmeet]
          omega
        have hprevV : previous.target.v = k - 1 := by
          rw [hmeet]
          omega
        obtain ⟨p, hp, hpu, hpv, hpw⟩ :=
          ih hprevU (k - 1) hprevV b hbpred
        exact ⟨p, LiteralEdgePath.Visits.ofPrefix hnext hmeet hlabel hp,
          hpu, hpv, hpw⟩

theorem labelOne_corner_path_visits_all_vertical
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hfirst : first.source = sourceOne (m + 3))
    (hlast : last.target = sourceZero (m + 3))
    (hlabel : last.boneClass.label = .one)
    (b : ℕ) (hb : b ≤ m + 3) :
    ∃ p : SimplexPoint (m + 3),
      path.Visits p ∧ p.u = 0 ∧ p.v = b ∧ p.w = m + 3 - b := by
  have hall := path.labelOne_all_steps_B hlabel (by simp [hlast, sourceZero])
  exact allB_path_visits_vertical_prefix hall
    (by simp [hfirst, sourceOne])
    (by simp [hfirst, sourceOne])
    (by simp [hlast, sourceZero])
    (m + 3) (by simp [hlast, sourceZero]) b hb

theorem LiteralEdgePath.Visits.source_or_incoming
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    {path : LiteralEdgePath hstone tiling first last}
    {p : SimplexPoint (m + 3)}
    (visit : path.Visits p) :
    p = first.source ∨
      ∃ edge ∈ literalDirectedEdges hstone tiling,
        edge.boneClass.label = first.boneClass.label ∧ edge.target = p := by
  induction visit with
  | source path => exact Or.inl rfl
  | singleTarget hedge => exact Or.inr ⟨first, hedge, rfl, rfl⟩
  | @ofPrefix previous next path hnext hmeet hlabel p hp ih =>
      rcases ih with hsource | ⟨edge, hedge, hedgeLabel, hedgeTarget⟩
      · exact Or.inl hsource
      · exact Or.inr ⟨edge, hedge, hedgeLabel, hedgeTarget⟩
  | @lastTarget previous next path hnext hmeet hlabel =>
      exact Or.inr ⟨next, hnext, (path.label_eq.trans hlabel).symm, rfl⟩

theorem allA_path_visits_horizontal_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    {path : LiteralEdgePath hstone tiling first last}
    (hall : path.AllEdges (fun edge => edge.boneClass.step = stepA))
    (hstartV : first.source.v = 0) (hstartW : first.source.w = 0)
    (hendV : last.target.v = 0)
    (k : ℕ) (hendW : last.target.w = k)
    (b : ℕ) (hb : b ≤ k) :
    ∃ p : SimplexPoint (m + 3),
      path.Visits p ∧ p.v = 0 ∧ p.w = b ∧ p.u = m + 3 - b := by
  induction hall generalizing k b with
  | single hedge hA =>
      have hanchor := literalDirectedEdge_anchor_step first
      rw [hA] at hanchor
      have hcoords := stepA_simplex_coordinates first.source first.target hanchor
      have hk : k = 1 := by omega
      subst k
      have hbCases : b = 0 ∨ b = 1 := by omega
      rcases hbCases with rfl | rfl
      · refine ⟨first.source, LiteralEdgePath.Visits.source
          (LiteralEdgePath.single first hedge), hstartV, hstartW, ?_⟩
        have hsum := first.source.sum_eq
        omega
      · refine ⟨first.target, LiteralEdgePath.Visits.singleTarget first hedge,
          hendV, by omega, ?_⟩
        have hsum := first.target.sum_eq
        omega
  | @snoc previous next path hall hnext hmeet hlabel hA ih =>
      have hanchor := literalDirectedEdge_anchor_step next
      rw [hA] at hanchor
      have hcoords := stepA_simplex_coordinates next.source next.target hanchor
      have hkpos : 0 < k := by omega
      by_cases hbk : b = k
      · subst b
        refine ⟨next.target,
          LiteralEdgePath.Visits.lastTarget path hnext hmeet hlabel,
          hendV, hendW, ?_⟩
        have hsum := next.target.sum_eq
        omega
      · have hbpred : b ≤ k - 1 := by omega
        have hprevV : previous.target.v = 0 := by rw [hmeet]; omega
        have hprevW : previous.target.w = k - 1 := by rw [hmeet]; omega
        obtain ⟨p, hp, hpv, hpw, hpu⟩ :=
          ih hprevV (k - 1) hprevW b hbpred
        exact ⟨p, LiteralEdgePath.Visits.ofPrefix hnext hmeet hlabel hp,
          hpv, hpw, hpu⟩

theorem allC_path_visits_diagonal_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    {path : LiteralEdgePath hstone tiling first last}
    (hall : path.AllEdges (fun edge => edge.boneClass.step = stepC))
    (hstartW : first.source.w = 0) (hstartU : first.source.u = 0)
    (hendW : last.target.w = 0)
    (k : ℕ) (hendU : last.target.u = k)
    (b : ℕ) (hb : b ≤ k) :
    ∃ p : SimplexPoint (m + 3),
      path.Visits p ∧ p.w = 0 ∧ p.u = b ∧ p.v = m + 3 - b := by
  induction hall generalizing k b with
  | single hedge hC =>
      have hanchor := literalDirectedEdge_anchor_step first
      rw [hC] at hanchor
      have hcoords := stepC_simplex_coordinates first.source first.target hanchor
      have hk : k = 1 := by omega
      subst k
      have hbCases : b = 0 ∨ b = 1 := by omega
      rcases hbCases with rfl | rfl
      · refine ⟨first.source, LiteralEdgePath.Visits.source
          (LiteralEdgePath.single first hedge), hstartW, hstartU, ?_⟩
        have hsum := first.source.sum_eq
        omega
      · refine ⟨first.target, LiteralEdgePath.Visits.singleTarget first hedge,
          hendW, by omega, ?_⟩
        have hsum := first.target.sum_eq
        omega
  | @snoc previous next path hall hnext hmeet hlabel hC ih =>
      have hanchor := literalDirectedEdge_anchor_step next
      rw [hC] at hanchor
      have hcoords := stepC_simplex_coordinates next.source next.target hanchor
      have hkpos : 0 < k := by omega
      by_cases hbk : b = k
      · subst b
        refine ⟨next.target,
          LiteralEdgePath.Visits.lastTarget path hnext hmeet hlabel,
          hendW, hendU, ?_⟩
        have hsum := next.target.sum_eq
        omega
      · have hbpred : b ≤ k - 1 := by omega
        have hprevW : previous.target.w = 0 := by rw [hmeet]; omega
        have hprevU : previous.target.u = k - 1 := by rw [hmeet]; omega
        obtain ⟨p, hp, hpw, hpu, hpv⟩ :=
          ih hprevW (k - 1) hprevU b hbpred
        exact ⟨p, LiteralEdgePath.Visits.ofPrefix hnext hmeet hlabel hp,
          hpw, hpu, hpv⟩

end BenzelProblem6Kernel
