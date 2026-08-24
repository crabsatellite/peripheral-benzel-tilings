import BenzelProblem6Kernel.YPathDisjointness
import BenzelProblem6Kernel.BallotWordSurjectivity

/-!
# Data-valued finite literal paths

`LiteralEdgePath` is intentionally proof-valued.  This parallel carrier lives
in `Type`, so its ordered edge sequence may be transported to a ballot word.
-/

namespace BenzelProblem6Kernel

inductive LiteralEdgePathData
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    LiteralDirectedEdge m → LiteralDirectedEdge m → Type
  | single (edge : LiteralDirectedEdge m)
      (hedge : edge ∈ literalDirectedEdges hstone tiling) :
      LiteralEdgePathData hstone tiling edge edge
  | snoc {first last next : LiteralDirectedEdge m}
      (path : LiteralEdgePathData hstone tiling first last)
      (hnext : next ∈ literalDirectedEdges hstone tiling)
      (hmeet : last.target = next.source)
      (hlabel : last.boneClass.label = next.boneClass.label) :
      LiteralEdgePathData hstone tiling first next

def LiteralEdgePathData.toPath
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m} :
    (first last : LiteralDirectedEdge m) →
      LiteralEdgePathData hstone tiling first last →
      LiteralEdgePath hstone tiling first last
  | _, _, .single edge hedge => LiteralEdgePath.single edge hedge
  | _, _, .snoc pathPrefix hnext hmeet hlabel =>
      LiteralEdgePath.snoc (toPath _ _ pathPrefix) hnext hmeet hlabel

def GoodBoneClass.ballotMove : GoodBoneClass → BallotMove
  | .boneA0 | .boneB1 | .boneC0 => .majority
  | .boneA2 | .boneB0 | .boneC2 => .minority

theorem goodBoneClass_ballotMove_majority_iff (boneClass : GoodBoneClass) :
    boneClass.ballotMove = .majority ↔
      (boneClass.label = .zero ∧ boneClass.step = stepC) ∨
      (boneClass.label = .one ∧ boneClass.step = stepB) ∨
      (boneClass.label = .two ∧ boneClass.step = stepA) := by
  rcases boneClass <;> decide

theorem goodBoneClass_ballotMove_minority_iff (boneClass : GoodBoneClass) :
    boneClass.ballotMove = .minority ↔
      (boneClass.label = .zero ∧ boneClass.step = stepA) ∨
      (boneClass.label = .one ∧ boneClass.step = stepC) ∨
      (boneClass.label = .two ∧ boneClass.step = stepB) := by
  rcases boneClass <;> decide

def LiteralEdgePathData.ballotWord
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m} :
    (first last : LiteralDirectedEdge m) →
      LiteralEdgePathData hstone tiling first last → List BallotMove
  | _, _, .single edge _ => [edge.boneClass.ballotMove]
  | _, _, .snoc (next := next) pathPrefix _ _ _ =>
      ballotWord _ _ pathPrefix ++ [next.boneClass.ballotMove]

theorem LiteralEdgePathData.toPath_label_eq
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    first.boneClass.label = last.boneClass.label :=
  (LiteralEdgePathData.toPath first last path).label_eq

theorem nonempty_corner_ancestor_pathData
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    ∃ rootEdge,
      Nonempty (LiteralEdgePathData hstone tiling rootEdge edge) ∧
      (rootEdge.source = sourceZero (m + 3) ∨
        rootEdge.source = sourceOne (m + 3) ∨
        rootEdge.source = sourceTwo (m + 3)) := by
  generalize hrank : simplexLabelRank edge.boneClass.label edge.source = rank
  induction rank using Nat.strong_induction_on generalizing edge with
  | h rank ih =>
      rcases simplex_corner_or_full (t := m + 3) (by omega) edge.source with
        hzero | hone | htwo | hfull
      · exact ⟨edge, ⟨LiteralEdgePathData.single edge hedge⟩, Or.inl hzero⟩
      · exact ⟨edge, ⟨LiteralEdgePathData.single edge hedge⟩,
          Or.inr (Or.inl hone)⟩
      · exact ⟨edge, ⟨LiteralEdgePathData.single edge hedge⟩,
          Or.inr (Or.inr htwo)⟩
      · obtain ⟨inEdge, hin, htarget, hlabel⟩ :=
          exists_incoming_same_label_at_full_source hstone tiling edge hedge
            hfull.1 hfull.2.1 hfull.2.2
        have hlt : simplexLabelRank inEdge.boneClass.label inEdge.source < rank := by
          have hlt' := incoming_rank_lt_source_rank inEdge edge htarget hlabel
          rw [hrank] at hlt'
          simpa [hlabel] using hlt'
        obtain ⟨rootEdge, ⟨pathPrefix⟩, hcorner⟩ := ih _ hlt inEdge hin rfl
        exact ⟨rootEdge,
          ⟨LiteralEdgePathData.snoc pathPrefix hedge htarget hlabel⟩, hcorner⟩

end BenzelProblem6Kernel
