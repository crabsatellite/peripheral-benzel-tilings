import BenzelProblem6Kernel.ArmPrefixBounds

/-!
# Natural simplex points carried by arm prefixes

The endpoint formulas are stated first in integer coordinates.  This file
packages every prefix of each of the six arm words as an actual simplex point,
without changing those coordinates.
-/

namespace BenzelProblem6Kernel

def IntSimplex.toSimplexPoint (t : ℕ) (point : IntSimplex)
    (hu : 0 ≤ point.u) (hv : 0 ≤ point.v) (hw : 0 ≤ point.w)
    (hsum : point.u + point.v + point.w = t) : SimplexPoint t where
  u := point.u.toNat
  v := point.v.toNat
  w := point.w.toNat
  sum_eq := by omega

@[simp] theorem IntSimplex.toSimplexPoint_u (t : ℕ) (point : IntSimplex)
    (hu : 0 ≤ point.u) (hv : 0 ≤ point.v) (hw : 0 ≤ point.w)
    (hsum : point.u + point.v + point.w = t) :
    ((point.toSimplexPoint t hu hv hw hsum).u : ℤ) = point.u := by
  simp [IntSimplex.toSimplexPoint, hu]

@[simp] theorem IntSimplex.toSimplexPoint_v (t : ℕ) (point : IntSimplex)
    (hu : 0 ≤ point.u) (hv : 0 ≤ point.v) (hw : 0 ≤ point.w)
    (hsum : point.u + point.v + point.w = t) :
    ((point.toSimplexPoint t hu hv hw hsum).v : ℤ) = point.v := by
  simp [IntSimplex.toSimplexPoint, hv]

@[simp] theorem IntSimplex.toSimplexPoint_w (t : ℕ) (point : IntSimplex)
    (hu : 0 ≤ point.u) (hv : 0 ≤ point.v) (hw : 0 ≤ point.w)
    (hsum : point.u + point.v + point.w = t) :
    ((point.toSimplexPoint t hu hv hw hsum).w : ℤ) = point.w := by
  simp [IntSimplex.toSimplexPoint, hw]

theorem labelZeroPrefixPoint_sum (t : ℕ) (word : List BallotMove) :
    (labelZeroPrefixPoint t word).u +
      (labelZeroPrefixPoint t word).v +
      (labelZeroPrefixPoint t word).w = t := by
  simp [labelZeroPrefixPoint]

theorem labelOnePrefixPoint_sum (t : ℕ) (word : List BallotMove) :
    (labelOnePrefixPoint t word).u +
      (labelOnePrefixPoint t word).v +
      (labelOnePrefixPoint t word).w = t := by
  simp [labelOnePrefixPoint]

theorem labelTwoPrefixPoint_sum (t : ℕ) (word : List BallotMove) :
    (labelTwoPrefixPoint t word).u +
      (labelTwoPrefixPoint t word).v +
      (labelTwoPrefixPoint t word).w = t := by
  simp [labelTwoPrefixPoint]

theorem labelZeroPrefixPoint_nonnegative {word : List BallotMove}
    (hballot : IsBallotSequence word) (t : ℕ)
    (hmajor : majorityCount word ≤ t) :
    0 ≤ (labelZeroPrefixPoint t word).u ∧
      0 ≤ (labelZeroPrefixPoint t word).v ∧
      0 ≤ (labelZeroPrefixPoint t word).w := by
  have hcount := hballot.count_le
  simp [labelZeroPrefixPoint]
  omega

theorem labelOnePrefixPoint_nonnegative {word : List BallotMove}
    (hballot : IsBallotSequence word) (t : ℕ)
    (hmajor : majorityCount word ≤ t) :
    0 ≤ (labelOnePrefixPoint t word).u ∧
      0 ≤ (labelOnePrefixPoint t word).v ∧
      0 ≤ (labelOnePrefixPoint t word).w := by
  have hcount := hballot.count_le
  simp [labelOnePrefixPoint]
  omega

theorem labelTwoPrefixPoint_nonnegative {word : List BallotMove}
    (hballot : IsBallotSequence word) (t : ℕ)
    (hmajor : majorityCount word ≤ t) :
    0 ≤ (labelTwoPrefixPoint t word).u ∧
      0 ≤ (labelTwoPrefixPoint t word).v ∧
      0 ≤ (labelTwoPrefixPoint t word).w := by
  have hcount := hballot.count_le
  simp [labelTwoPrefixPoint]
  omega

noncomputable def labelZeroPrefixSimplexPoint {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    SimplexPoint t := by
  have hballot := (recursiveBallotWord_isBallot path).prefix_closed hp
  have hmajor : majorityCount pre ≤ t := by
    have := majorityCount_prefix_le hp
    rw [recursiveBallotWord_majority path] at this
    omega
  have hnonneg := labelZeroPrefixPoint_nonnegative hballot t hmajor
  exact (labelZeroPrefixPoint t pre).toSimplexPoint t
    hnonneg.1 hnonneg.2.1 hnonneg.2.2 (labelZeroPrefixPoint_sum t pre)

noncomputable def labelOnePrefixSimplexPoint {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    SimplexPoint t := by
  have hballot := (recursiveBallotWord_isBallot path).prefix_closed hp
  have hmajor : majorityCount pre ≤ t := by
    have := majorityCount_prefix_le hp
    rw [recursiveBallotWord_majority path] at this
    omega
  have hnonneg := labelOnePrefixPoint_nonnegative hballot t hmajor
  exact (labelOnePrefixPoint t pre).toSimplexPoint t
    hnonneg.1 hnonneg.2.1 hnonneg.2.2 (labelOnePrefixPoint_sum t pre)

noncomputable def labelTwoPrefixSimplexPoint {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    SimplexPoint t := by
  have hballot := (recursiveBallotWord_isBallot path).prefix_closed hp
  have hmajor : majorityCount pre ≤ t := by
    have := majorityCount_prefix_le hp
    rw [recursiveBallotWord_majority path] at this
    omega
  have hnonneg := labelTwoPrefixPoint_nonnegative hballot t hmajor
  exact (labelTwoPrefixPoint t pre).toSimplexPoint t
    hnonneg.1 hnonneg.2.1 hnonneg.2.2 (labelTwoPrefixPoint_sum t pre)

@[simp] theorem labelZeroPrefixSimplexPoint_u {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelZeroPrefixSimplexPoint path pre hp hup).u : ℤ) =
      (labelZeroPrefixPoint t pre).u := by
  simp [labelZeroPrefixSimplexPoint]

@[simp] theorem labelZeroPrefixSimplexPoint_v {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelZeroPrefixSimplexPoint path pre hp hup).v : ℤ) =
      (labelZeroPrefixPoint t pre).v := by
  simp [labelZeroPrefixSimplexPoint]

@[simp] theorem labelZeroPrefixSimplexPoint_w {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelZeroPrefixSimplexPoint path pre hp hup).w : ℤ) =
      (labelZeroPrefixPoint t pre).w := by
  simp [labelZeroPrefixSimplexPoint]

@[simp] theorem labelOnePrefixSimplexPoint_u {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelOnePrefixSimplexPoint path pre hp hup).u : ℤ) =
      (labelOnePrefixPoint t pre).u := by
  simp [labelOnePrefixSimplexPoint]

@[simp] theorem labelOnePrefixSimplexPoint_v {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelOnePrefixSimplexPoint path pre hp hup).v : ℤ) =
      (labelOnePrefixPoint t pre).v := by
  simp [labelOnePrefixSimplexPoint]

@[simp] theorem labelOnePrefixSimplexPoint_w {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelOnePrefixSimplexPoint path pre hp hup).w : ℤ) =
      (labelOnePrefixPoint t pre).w := by
  simp [labelOnePrefixSimplexPoint]

@[simp] theorem labelTwoPrefixSimplexPoint_u {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelTwoPrefixSimplexPoint path pre hp hup).u : ℤ) =
      (labelTwoPrefixPoint t pre).u := by
  simp [labelTwoPrefixSimplexPoint]

@[simp] theorem labelTwoPrefixSimplexPoint_v {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelTwoPrefixSimplexPoint path pre hp hup).v : ℤ) =
      (labelTwoPrefixPoint t pre).v := by
  simp [labelTwoPrefixSimplexPoint]

@[simp] theorem labelTwoPrefixSimplexPoint_w {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    ((labelTwoPrefixSimplexPoint path pre hp hup).w : ℤ) =
      (labelTwoPrefixPoint t pre).w := by
  simp [labelTwoPrefixSimplexPoint]

@[simp] theorem labelZeroPrefixSimplexPoint_coordinates {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    (((labelZeroPrefixSimplexPoint path pre hp hup).u : ℤ),
      ((labelZeroPrefixSimplexPoint path pre hp hup).v : ℤ),
      ((labelZeroPrefixSimplexPoint path pre hp hup).w : ℤ)) =
        ((labelZeroPrefixPoint t pre).u,
          (labelZeroPrefixPoint t pre).v,
          (labelZeroPrefixPoint t pre).w) := by
  simp [labelZeroPrefixSimplexPoint]

@[simp] theorem labelOnePrefixSimplexPoint_coordinates {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    (((labelOnePrefixSimplexPoint path pre hp hup).u : ℤ),
      ((labelOnePrefixSimplexPoint path pre hp hup).v : ℤ),
      ((labelOnePrefixSimplexPoint path pre hp hup).w : ℤ)) =
        ((labelOnePrefixPoint t pre).u,
          (labelOnePrefixPoint t pre).v,
          (labelOnePrefixPoint t pre).w) := by
  simp [labelOnePrefixSimplexPoint]

@[simp] theorem labelTwoPrefixSimplexPoint_coordinates {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    (((labelTwoPrefixSimplexPoint path pre hp hup).u : ℤ),
      ((labelTwoPrefixSimplexPoint path pre hp hup).v : ℤ),
      ((labelTwoPrefixSimplexPoint path pre hp hup).w : ℤ)) =
        ((labelTwoPrefixPoint t pre).u,
          (labelTwoPrefixPoint t pre).v,
          (labelTwoPrefixPoint t pre).w) := by
  simp [labelTwoPrefixSimplexPoint]

end BenzelProblem6Kernel
