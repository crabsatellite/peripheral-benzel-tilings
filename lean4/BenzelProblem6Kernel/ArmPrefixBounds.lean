import BenzelProblem6Kernel.ArmEndpoints

/-!
# Prefix bounds and automatic disjointness of fixed-sink arms
-/

namespace BenzelProblem6Kernel

theorem positive_labelZero_prefix_bounds (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1))
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    0 ≤ (labelZeroPrefixPoint (x + y + z + 3) pre).u ∧
    (y + 2 : ℤ) ≤ (labelZeroPrefixPoint (x + y + z + 3) pre).v ∧
    (labelZeroPrefixPoint (x + y + z + 3) pre).w ≤ z + 1 := by
  have hballot := recursiveBallotPrefix_count_le path pre hp
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  simp [labelZeroPrefixPoint]
  omega

theorem negative_labelZero_prefix_bounds (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    0 ≤ (labelZeroPrefixPoint (x + y + z + 3) pre).u ∧
    (y + 1 : ℤ) ≤ (labelZeroPrefixPoint (x + y + z + 3) pre).v ∧
    (labelZeroPrefixPoint (x + y + z + 3) pre).w ≤ z := by
  have hballot := recursiveBallotPrefix_count_le path pre hp
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  simp [labelZeroPrefixPoint]
  omega

theorem positive_labelOne_prefix_bounds (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1))
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    (labelOnePrefixPoint (x + y + z + 3) pre).u ≤ x + 1 ∧
    0 ≤ (labelOnePrefixPoint (x + y + z + 3) pre).v ∧
    (z + 2 : ℤ) ≤ (labelOnePrefixPoint (x + y + z + 3) pre).w := by
  have hballot := recursiveBallotPrefix_count_le path pre hp
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  simp [labelOnePrefixPoint]
  omega

theorem negative_labelOne_prefix_bounds (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    (labelOnePrefixPoint (x + y + z + 3) pre).u ≤ x ∧
    0 ≤ (labelOnePrefixPoint (x + y + z + 3) pre).v ∧
    (z + 1 : ℤ) ≤ (labelOnePrefixPoint (x + y + z + 3) pre).w := by
  have hballot := recursiveBallotPrefix_count_le path pre hp
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  simp [labelOnePrefixPoint]
  omega

theorem positive_labelTwo_prefix_bounds (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1))
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    (x + 2 : ℤ) ≤ (labelTwoPrefixPoint (x + y + z + 3) pre).u ∧
    (labelTwoPrefixPoint (x + y + z + 3) pre).v ≤ y + 1 ∧
    0 ≤ (labelTwoPrefixPoint (x + y + z + 3) pre).w := by
  have hballot := recursiveBallotPrefix_count_le path pre hp
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  simp [labelTwoPrefixPoint]
  omega

theorem negative_labelTwo_prefix_bounds (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    (x + 1 : ℤ) ≤ (labelTwoPrefixPoint (x + y + z + 3) pre).u ∧
    (labelTwoPrefixPoint (x + y + z + 3) pre).v ≤ y ∧
    0 ≤ (labelTwoPrefixPoint (x + y + z + 3) pre).w := by
  have hballot := recursiveBallotPrefix_count_le path pre hp
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  simp [labelTwoPrefixPoint]
  omega

def PositiveLabelZeroPoint (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1))
    (point : IntSimplex) : Prop :=
  point = intSink x y z ∨
    ∃ pre, pre <+: recursiveBallotWord path ∧
      point = labelZeroPrefixPoint (x + y + z + 3) pre

def PositiveLabelOnePoint (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1))
    (point : IntSimplex) : Prop :=
  point = intSink x y z ∨
    ∃ pre, pre <+: recursiveBallotWord path ∧
      point = labelOnePrefixPoint (x + y + z + 3) pre

def PositiveLabelTwoPoint (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1))
    (point : IntSimplex) : Prop :=
  point = intSink x y z ∨
    ∃ pre, pre <+: recursiveBallotWord path ∧
      point = labelTwoPrefixPoint (x + y + z + 3) pre

def NegativeLabelZeroPoint (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z)
    (point : IntSimplex) : Prop :=
  point = intSink x y z ∨
    ∃ pre, pre <+: recursiveBallotWord path ∧
      point = labelZeroPrefixPoint (x + y + z + 3) pre

def NegativeLabelOnePoint (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x)
    (point : IntSimplex) : Prop :=
  point = intSink x y z ∨
    ∃ pre, pre <+: recursiveBallotWord path ∧
      point = labelOnePrefixPoint (x + y + z + 3) pre

def NegativeLabelTwoPoint (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y)
    (point : IntSimplex) : Prop :=
  point = intSink x y z ∨
    ∃ pre, pre <+: recursiveBallotWord path ∧
      point = labelTwoPrefixPoint (x + y + z + 3) pre

theorem positive_arms_zero_one_meet_only_at_sink (x y z : ℕ)
    (path0 : RecursiveBallot (x + z + 1) (z + 1))
    (path1 : RecursiveBallot (x + y + 1) (x + 1))
    (point : IntSimplex)
    (h0 : PositiveLabelZeroPoint x y z path0 point)
    (h1 : PositiveLabelOnePoint x y z path1 point) :
    point = intSink x y z := by
  rcases h0 with hsink | ⟨pre0, hp0, rfl⟩
  · exact hsink
  rcases h1 with hsink | ⟨pre1, hp1, heq⟩
  · exact hsink
  have hbound0 := positive_labelZero_prefix_bounds x y z path0 pre0 hp0
  have hbound1 := positive_labelOne_prefix_bounds x y z path1 pre1 hp1
  have hw := congrArg IntSimplex.w heq
  omega

theorem positive_arms_one_two_meet_only_at_sink (x y z : ℕ)
    (path1 : RecursiveBallot (x + y + 1) (x + 1))
    (path2 : RecursiveBallot (y + z + 1) (y + 1))
    (point : IntSimplex)
    (h1 : PositiveLabelOnePoint x y z path1 point)
    (h2 : PositiveLabelTwoPoint x y z path2 point) :
    point = intSink x y z := by
  rcases h1 with hsink | ⟨pre1, hp1, rfl⟩
  · exact hsink
  rcases h2 with hsink | ⟨pre2, hp2, heq⟩
  · exact hsink
  have hbound1 := positive_labelOne_prefix_bounds x y z path1 pre1 hp1
  have hbound2 := positive_labelTwo_prefix_bounds x y z path2 pre2 hp2
  have hu := congrArg IntSimplex.u heq
  omega

theorem positive_arms_two_zero_meet_only_at_sink (x y z : ℕ)
    (path2 : RecursiveBallot (y + z + 1) (y + 1))
    (path0 : RecursiveBallot (x + z + 1) (z + 1))
    (point : IntSimplex)
    (h2 : PositiveLabelTwoPoint x y z path2 point)
    (h0 : PositiveLabelZeroPoint x y z path0 point) :
    point = intSink x y z := by
  rcases h2 with hsink | ⟨pre2, hp2, rfl⟩
  · exact hsink
  rcases h0 with hsink | ⟨pre0, hp0, heq⟩
  · exact hsink
  have hbound2 := positive_labelTwo_prefix_bounds x y z path2 pre2 hp2
  have hbound0 := positive_labelZero_prefix_bounds x y z path0 pre0 hp0
  have hv := congrArg IntSimplex.v heq
  omega

theorem negative_arms_zero_one_meet_only_at_sink (x y z : ℕ)
    (path0 : RecursiveBallot (x + z + 2) z)
    (path1 : RecursiveBallot (x + y + 2) x)
    (point : IntSimplex)
    (h0 : NegativeLabelZeroPoint x y z path0 point)
    (h1 : NegativeLabelOnePoint x y z path1 point) :
    point = intSink x y z := by
  rcases h0 with hsink | ⟨pre0, hp0, rfl⟩
  · exact hsink
  rcases h1 with hsink | ⟨pre1, hp1, heq⟩
  · exact hsink
  have hbound0 := negative_labelZero_prefix_bounds x y z path0 pre0 hp0
  have hbound1 := negative_labelOne_prefix_bounds x y z path1 pre1 hp1
  have hw := congrArg IntSimplex.w heq
  omega

theorem negative_arms_one_two_meet_only_at_sink (x y z : ℕ)
    (path1 : RecursiveBallot (x + y + 2) x)
    (path2 : RecursiveBallot (y + z + 2) y)
    (point : IntSimplex)
    (h1 : NegativeLabelOnePoint x y z path1 point)
    (h2 : NegativeLabelTwoPoint x y z path2 point) :
    point = intSink x y z := by
  rcases h1 with hsink | ⟨pre1, hp1, rfl⟩
  · exact hsink
  rcases h2 with hsink | ⟨pre2, hp2, heq⟩
  · exact hsink
  have hbound1 := negative_labelOne_prefix_bounds x y z path1 pre1 hp1
  have hbound2 := negative_labelTwo_prefix_bounds x y z path2 pre2 hp2
  have hu := congrArg IntSimplex.u heq
  omega

theorem negative_arms_two_zero_meet_only_at_sink (x y z : ℕ)
    (path2 : RecursiveBallot (y + z + 2) y)
    (path0 : RecursiveBallot (x + z + 2) z)
    (point : IntSimplex)
    (h2 : NegativeLabelTwoPoint x y z path2 point)
    (h0 : NegativeLabelZeroPoint x y z path0 point) :
    point = intSink x y z := by
  rcases h2 with hsink | ⟨pre2, hp2, rfl⟩
  · exact hsink
  rcases h0 with hsink | ⟨pre0, hp0, heq⟩
  · exact hsink
  have hbound2 := negative_labelTwo_prefix_bounds x y z path2 pre2 hp2
  have hbound0 := negative_labelZero_prefix_bounds x y z path0 pre0 hp0
  have hv := congrArg IntSimplex.v heq
  omega

end BenzelProblem6Kernel
