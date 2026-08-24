import BenzelProblem6Kernel.ReconstructedYPlacements

/-!
# Prefix vertices are injective along each reconstructed arm
-/

namespace BenzelProblem6Kernel

theorem majorityCount_add_minorityCount (word : List BallotMove) :
    majorityCount word + minorityCount word = word.length := by
  induction word with
  | nil => simp [majorityCount, minorityCount]
  | cons move word ih =>
      rcases move <;>
        simp [majorityCount, minorityCount] at ih ⊢ <;>
        omega

private theorem prefixes_eq_of_counts_eq {word left right : List BallotMove}
    (hl : left <+: word) (hr : right <+: word)
    (hmajor : majorityCount left = majorityCount right)
    (hminor : minorityCount left = minorityCount right) : left = right := by
  have hlen : left.length = right.length := by
    have hlcount := majorityCount_add_minorityCount left
    have hrcount := majorityCount_add_minorityCount right
    omega
  have hleft := List.prefix_iff_eq_take.mp hl
  have hright := List.prefix_iff_eq_take.mp hr
  rw [hleft, hright, hlen]

theorem labelZeroPrefixPoint_injective {up down t : ℕ}
    (path : RecursiveBallot up down)
    (left right : List BallotMove)
    (hl : left <+: recursiveBallotWord path)
    (hr : right <+: recursiveBallotWord path)
    (heq : labelZeroPrefixPoint t left = labelZeroPrefixPoint t right) :
    left = right := by
  have hu := congrArg IntSimplex.u heq
  have hw := congrArg IntSimplex.w heq
  simp [labelZeroPrefixPoint] at hu hw
  apply prefixes_eq_of_counts_eq hl hr
  · omega
  · omega

theorem labelOnePrefixPoint_injective {up down t : ℕ}
    (path : RecursiveBallot up down)
    (left right : List BallotMove)
    (hl : left <+: recursiveBallotWord path)
    (hr : right <+: recursiveBallotWord path)
    (heq : labelOnePrefixPoint t left = labelOnePrefixPoint t right) :
    left = right := by
  have hu := congrArg IntSimplex.u heq
  have hv := congrArg IntSimplex.v heq
  simp [labelOnePrefixPoint] at hu hv
  apply prefixes_eq_of_counts_eq hl hr
  · omega
  · omega

theorem labelTwoPrefixPoint_injective {up down t : ℕ}
    (path : RecursiveBallot up down)
    (left right : List BallotMove)
    (hl : left <+: recursiveBallotWord path)
    (hr : right <+: recursiveBallotWord path)
    (heq : labelTwoPrefixPoint t left = labelTwoPrefixPoint t right) :
    left = right := by
  have hv := congrArg IntSimplex.v heq
  have hw := congrArg IntSimplex.w heq
  simp [labelTwoPrefixPoint] at hv hw
  apply prefixes_eq_of_counts_eq hl hr
  · omega
  · omega

theorem simplexPointToInt_injective {t : ℕ}
    {left right : SimplexPoint t}
    (heq : simplexPointToInt left = simplexPointToInt right) : left = right := by
  apply simplexPoint_ext
  · have hu := congrArg IntSimplex.u heq
    simp [simplexPointToInt] at hu
    omega
  · have hv := congrArg IntSimplex.v heq
    simp [simplexPointToInt] at hv
    omega
  · have hw := congrArg IntSimplex.w heq
    simp [simplexPointToInt] at hw
    omega

theorem simplexPointToInt_eq_intSink_iff (x y z : ℕ)
    (point : SimplexPoint (x + y + z + 3)) :
    simplexPointToInt point = intSink x y z ↔ point = sinkPoint x y z := by
  constructor
  · intro heq
    apply simplexPoint_ext
    · have := congrArg IntSimplex.u heq
      simp [simplexPointToInt, intSink, sinkPoint] at this
      change point.u = x + 1
      omega
    · have := congrArg IntSimplex.v heq
      simp [simplexPointToInt, intSink, sinkPoint] at this
      change point.v = y + 1
      omega
    · have := congrArg IntSimplex.w heq
      simp [simplexPointToInt, intSink, sinkPoint] at this
      change point.w = z + 1
      omega
  · rintro rfl
    simp [simplexPointToInt, intSink, sinkPoint]

theorem positive_zero_one_owner_meet_only_at_sink (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (hzero : PositiveLabelZeroPoint x y z arms.1
      (simplexPointToInt point))
    (hone : PositiveLabelOnePoint x y z arms.2.1
      (simplexPointToInt point)) :
    point = sinkPoint x y z := by
  apply (simplexPointToInt_eq_intSink_iff x y z point).1
  exact positive_arms_zero_one_meet_only_at_sink x y z
    arms.1 arms.2.1 (simplexPointToInt point) hzero hone

theorem positive_one_two_owner_meet_only_at_sink (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (hone : PositiveLabelOnePoint x y z arms.2.1
      (simplexPointToInt point))
    (htwo : PositiveLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point)) :
    point = sinkPoint x y z := by
  apply (simplexPointToInt_eq_intSink_iff x y z point).1
  exact positive_arms_one_two_meet_only_at_sink x y z
    arms.2.1 arms.2.2 (simplexPointToInt point) hone htwo

theorem positive_two_zero_owner_meet_only_at_sink (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (htwo : PositiveLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point))
    (hzero : PositiveLabelZeroPoint x y z arms.1
      (simplexPointToInt point)) :
    point = sinkPoint x y z := by
  apply (simplexPointToInt_eq_intSink_iff x y z point).1
  exact positive_arms_two_zero_meet_only_at_sink x y z
    arms.2.2 arms.1 (simplexPointToInt point) htwo hzero

theorem negative_zero_one_owner_meet_only_at_sink (x y z : ℕ)
    (arms : NegativeArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (hzero : NegativeLabelZeroPoint x y z arms.1
      (simplexPointToInt point))
    (hone : NegativeLabelOnePoint x y z arms.2.1
      (simplexPointToInt point)) :
    point = sinkPoint x y z := by
  apply (simplexPointToInt_eq_intSink_iff x y z point).1
  exact negative_arms_zero_one_meet_only_at_sink x y z
    arms.1 arms.2.1 (simplexPointToInt point) hzero hone

theorem negative_one_two_owner_meet_only_at_sink (x y z : ℕ)
    (arms : NegativeArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (hone : NegativeLabelOnePoint x y z arms.2.1
      (simplexPointToInt point))
    (htwo : NegativeLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point)) :
    point = sinkPoint x y z := by
  apply (simplexPointToInt_eq_intSink_iff x y z point).1
  exact negative_arms_one_two_meet_only_at_sink x y z
    arms.2.1 arms.2.2 (simplexPointToInt point) hone htwo

theorem negative_two_zero_owner_meet_only_at_sink (x y z : ℕ)
    (arms : NegativeArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (htwo : NegativeLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point))
    (hzero : NegativeLabelZeroPoint x y z arms.1
      (simplexPointToInt point)) :
    point = sinkPoint x y z := by
  apply (simplexPointToInt_eq_intSink_iff x y z point).1
  exact negative_arms_two_zero_meet_only_at_sink x y z
    arms.2.2 arms.1 (simplexPointToInt point) htwo hzero

end BenzelProblem6Kernel
