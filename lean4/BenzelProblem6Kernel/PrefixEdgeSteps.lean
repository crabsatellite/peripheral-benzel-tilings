import BenzelProblem6Kernel.PrefixSimplexPoints
import BenzelProblem6Kernel.ReverseBonePlacement

/-!
# Adjacent arm prefixes are the required labelled simplex edges
-/

namespace BenzelProblem6Kernel

theorem labelZeroPrefix_owner_step {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path) (hup : up ≤ t) :
    addCell
      (ownerQ (labelZeroPrefixSimplexPoint path pre
        ((List.prefix_append pre [move]).trans hp) hup),
       ownerR (labelZeroPrefixSimplexPoint path pre
        ((List.prefix_append pre [move]).trans hp) hup))
      (goodBoneClassOfMove .zero move).step =
      (ownerQ (labelZeroPrefixSimplexPoint path (pre ++ [move]) hp hup),
       ownerR (labelZeroPrefixSimplexPoint path (pre ++ [move]) hp hup)) := by
  have hcount := recursiveBallotPrefix_count_le path pre
    ((List.prefix_append pre [move]).trans hp)
  have hmajor := majorityCount_prefix_le
    ((List.prefix_append pre [move]).trans hp)
  rw [recursiveBallotWord_majority path] at hmajor
  simp [majorityCount, minorityCount] at hcount hmajor
  rcases move <;> apply Prod.ext <;>
    simp [ownerQ, ownerR, addCell, goodBoneClassOfMove,
      GoodBoneClass.step,
      labelZeroPrefixPoint, majorityCount, minorityCount, stepA, stepC] <;>
    omega

theorem labelOnePrefix_owner_step {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path) (hup : up ≤ t) :
    addCell
      (ownerQ (labelOnePrefixSimplexPoint path pre
        ((List.prefix_append pre [move]).trans hp) hup),
       ownerR (labelOnePrefixSimplexPoint path pre
        ((List.prefix_append pre [move]).trans hp) hup))
      (goodBoneClassOfMove .one move).step =
      (ownerQ (labelOnePrefixSimplexPoint path (pre ++ [move]) hp hup),
       ownerR (labelOnePrefixSimplexPoint path (pre ++ [move]) hp hup)) := by
  have hcount := recursiveBallotPrefix_count_le path pre
    ((List.prefix_append pre [move]).trans hp)
  have hmajor := majorityCount_prefix_le
    ((List.prefix_append pre [move]).trans hp)
  rw [recursiveBallotWord_majority path] at hmajor
  simp [majorityCount, minorityCount] at hcount hmajor
  rcases move <;> apply Prod.ext <;>
    simp [ownerQ, ownerR, addCell, goodBoneClassOfMove,
      GoodBoneClass.step,
      labelOnePrefixPoint, majorityCount, minorityCount, stepB, stepC] <;>
    omega

theorem labelTwoPrefix_owner_step {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path) (hup : up ≤ t) :
    addCell
      (ownerQ (labelTwoPrefixSimplexPoint path pre
        ((List.prefix_append pre [move]).trans hp) hup),
       ownerR (labelTwoPrefixSimplexPoint path pre
        ((List.prefix_append pre [move]).trans hp) hup))
      (goodBoneClassOfMove .two move).step =
      (ownerQ (labelTwoPrefixSimplexPoint path (pre ++ [move]) hp hup),
       ownerR (labelTwoPrefixSimplexPoint path (pre ++ [move]) hp hup)) := by
  have hcount := recursiveBallotPrefix_count_le path pre
    ((List.prefix_append pre [move]).trans hp)
  have hmajor := majorityCount_prefix_le
    ((List.prefix_append pre [move]).trans hp)
  rw [recursiveBallotWord_majority path] at hmajor
  simp [majorityCount, minorityCount] at hcount hmajor
  rcases move <;> apply Prod.ext <;>
    simp [ownerQ, ownerR, addCell, goodBoneClassOfMove,
      GoodBoneClass.step,
      labelTwoPrefixPoint, majorityCount, minorityCount, stepA, stepB] <;>
    omega

end BenzelProblem6Kernel
