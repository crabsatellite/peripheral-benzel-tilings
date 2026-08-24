import BenzelProblem6Kernel.RemainingPlacementBoundaryInvariant

/-! # Bipartite parity of continuous honeycomb edge paths -/

namespace BenzelProblem6Kernel

def hexVertexClassZero (vertex : HexVertex) : Bool :=
  decide ((vertex.1 + vertex.2) % 3 = 0)

def AlternatesHexVertexClass (edge : LabeledHexEdge) : Prop :=
  hexVertexClassZero edge.source ≠ hexVertexClassZero edge.target

theorem cellBoundaryEdgeAt_alternates
    (cell : Cell) (side : HexSide) :
    AlternatesHexVertexClass (cellBoundaryEdgeAt cell side) := by
  rcases cell with ⟨i, j⟩
  cases side <;>
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC] <;> omega

inductive ContinuousLabeledEdgePath :
    HexVertex → List LabeledHexEdge → HexVertex → Prop
  | nil (vertex : HexVertex) :
      ContinuousLabeledEdgePath vertex [] vertex
  | cons (edge : LabeledHexEdge) {rest : List LabeledHexEdge}
      {target : HexVertex}
      (tail : ContinuousLabeledEdgePath edge.target rest target) :
      ContinuousLabeledEdgePath edge.source (edge :: rest) target

def labeledHexWalkEnd : HexVertex → List LabeledHexStep → HexVertex
  | source, [] => source
  | source, step :: rest =>
      labeledHexWalkEnd (addHexStep source step.1) rest

theorem walkLabeledHexEdges_continuous
    (source : HexVertex) (steps : List LabeledHexStep) :
    ContinuousLabeledEdgePath source
      (walkLabeledHexEdges source steps)
      (labeledHexWalkEnd source steps) := by
  induction steps generalizing source with
  | nil => exact .nil _
  | cons step rest ih =>
      exact .cons (advanceLabeledHexEdge source step.1 step.2)
        (ih (addHexStep source step.1))

theorem ContinuousLabeledEdgePath.append
    {start middle finish : HexVertex}
    {left right : List LabeledHexEdge}
    (hleft : ContinuousLabeledEdgePath start left middle)
    (hright : ContinuousLabeledEdgePath middle right finish) :
    ContinuousLabeledEdgePath start (left ++ right) finish := by
  induction hleft with
  | nil => exact hright
  | cons edge tail ih => exact .cons edge (ih hright)

theorem ContinuousLabeledEdgePath.reverse
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish) :
    ContinuousLabeledEdgePath finish
      (edges.reverse.map reverseLabeledHexEdge) start := by
  induction path with
  | nil => exact .nil _
  | cons edge tail ih =>
      rw [List.reverse_cons, List.map_append]
      apply ih.append
      exact .cons (reverseLabeledHexEdge edge) (.nil _)

theorem ContinuousLabeledEdgePath.prefix_before_edge
    {start finish : HexVertex} {segment suffix : List LabeledHexEdge}
    {edge : LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start
      (segment ++ edge :: suffix) finish) :
    ContinuousLabeledEdgePath start segment edge.source := by
  induction segment generalizing start with
  | nil =>
      cases path with
      | cons _ tail => exact .nil _
  | cons head rest ih =>
      cases path with
      | cons _ tail =>
          exact .cons head (ih tail)

theorem ContinuousLabeledEdgePath.suffix_after_edge
    {start finish : HexVertex} {segment suffix : List LabeledHexEdge}
    {edge : LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start
      (segment ++ edge :: suffix) finish) :
    ContinuousLabeledEdgePath edge.target suffix finish := by
  induction segment generalizing start with
  | nil =>
      cases path with
      | cons _ tail => exact tail
  | cons head rest ih =>
      cases path with
      | cons _ tail => exact ih tail

theorem reverseLabeledHexEdge_alternates
    {edge : LabeledHexEdge} (h : AlternatesHexVertexClass edge) :
    AlternatesHexVertexClass (reverseLabeledHexEdge edge) := by
  exact Ne.symm h

theorem ContinuousLabeledEdgePath.class_eq_iff_even
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (halternates : ∀ edge ∈ edges, AlternatesHexVertexClass edge) :
    hexVertexClassZero start = hexVertexClassZero finish ↔
      Even edges.length := by
  induction path with
  | nil vertex => simp
  | cons edge tail ih =>
      have hedge := halternates edge (by simp)
      have ih' := ih (fun item hitem =>
        halternates item (by simp [hitem]))
      rw [List.length_cons, Nat.even_add_one]
      cases hsource : hexVertexClassZero edge.source <;>
        cases htarget : hexVertexClassZero edge.target <;>
        cases hfinish : hexVertexClassZero finish <;>
        cases htailClass : hexVertexClassZero _ <;>
        simp [AlternatesHexVertexClass, hsource, htarget] at hedge <;>
        simp [hsource, htarget, hfinish, htailClass,
          Nat.not_even_iff_odd] at ih' ⊢
      all_goals assumption

theorem even_prefix_sum_of_common_endpoint
    {start₀ start₁ endpoint : HexVertex}
    {prefix₀ prefix₁ : List LabeledHexEdge}
    (path₀ : ContinuousLabeledEdgePath start₀ prefix₀ endpoint)
    (path₁ : ContinuousLabeledEdgePath start₁ prefix₁ endpoint)
    (hstart : hexVertexClassZero start₀ = hexVertexClassZero start₁)
    (halt₀ : ∀ edge ∈ prefix₀, AlternatesHexVertexClass edge)
    (halt₁ : ∀ edge ∈ prefix₁, AlternatesHexVertexClass edge) :
    Even (prefix₀.length + prefix₁.length) := by
  have heven₀ := path₀.class_eq_iff_even halt₀
  have heven₁ := path₁.class_eq_iff_even halt₁
  have hsame : Even prefix₀.length ↔ Even prefix₁.length := by
    rw [← heven₀, ← heven₁, hstart]
  rcases Nat.even_or_odd' prefix₀.length with ⟨k₀, hk₀ | hk₀⟩
  · have he₁ : Even prefix₁.length := hsame.mp ⟨k₀, by omega⟩
    obtain ⟨k₁, hk₁⟩ := he₁
    exact ⟨k₀ + k₁, by omega⟩
  · have hnotEven₀ : ¬Even prefix₀.length := by
      rw [hk₀]
      exact Nat.not_even_iff_odd.mpr ⟨k₀, by omega⟩
    have hnotEven₁ : ¬Even prefix₁.length := by
      exact fun he₁ => hnotEven₀ (hsame.mpr he₁)
    obtain ⟨k₁, hk₁⟩ := Nat.not_even_iff_odd.mp hnotEven₁
    exact ⟨k₀ + k₁ + 1, by omega⟩

theorem labeledEdgeWord_length (edges : List LabeledHexEdge) :
    (labeledEdgeWord edges).length = edges.length := by
  simp [labeledEdgeWord]

theorem evenShadowWord_of_even_edgePrefixSum
    (prefix₀ prefix₁ : List LabeledHexEdge)
    (heven : Even (prefix₀.length + prefix₁.length)) :
    EvenShadowLabelWord
      (labeledEdgeWord prefix₀ ++
        (labeledEdgeWord prefix₁).reverse) := by
  obtain ⟨half, hhalf⟩ := heven
  refine ⟨half, ?_⟩
  simp [labeledEdgeWord_length]
  omega

end BenzelProblem6Kernel
