import BenzelProblem6Kernel.LiteralPathBallot
import BenzelProblem6Kernel.YChirality

/-!
# Removing the prescribed final edge from a literal path word
-/

namespace BenzelProblem6Kernel

def LiteralEdgePathData.armWord
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) : List BallotMove :=
  (LiteralEdgePathData.ballotWord first last path).dropLast

theorem LiteralEdgePathData.ballotWord_eq_armWord_append_last
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    path.armWord ++ [last.boneClass.ballotMove] =
      LiteralEdgePathData.ballotWord first last path := by
  cases path <;>
    simp [LiteralEdgePathData.armWord, LiteralEdgePathData.ballotWord]

theorem LiteralEdgePathData.armWord_isBallot
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hballot : IsBallotSequence
      (LiteralEdgePathData.ballotWord first last path)) :
    IsBallotSequence path.armWord := by
  exact hballot.prefix_closed (by
    exact List.dropLast_prefix
      (LiteralEdgePathData.ballotWord first last path))

theorem LiteralEdgePathData.armWord_counts_of_last_majority
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlast : last.boneClass.ballotMove = .majority) :
    majorityCount path.armWord + 1 =
        majorityCount (LiteralEdgePathData.ballotWord first last path) ∧
      minorityCount path.armWord =
        minorityCount (LiteralEdgePathData.ballotWord first last path) := by
  rw [← path.ballotWord_eq_armWord_append_last]
  simp [hlast, majorityCount, minorityCount]

theorem LiteralEdgePathData.armWord_counts_of_last_minority
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlast : last.boneClass.ballotMove = .minority) :
    majorityCount path.armWord =
        majorityCount (LiteralEdgePathData.ballotWord first last path) ∧
      minorityCount path.armWord + 1 =
        minorityCount (LiteralEdgePathData.ballotWord first last path) := by
  rw [← path.ballotWord_eq_armWord_append_last]
  simp [hlast, majorityCount, minorityCount]

end BenzelProblem6Kernel
