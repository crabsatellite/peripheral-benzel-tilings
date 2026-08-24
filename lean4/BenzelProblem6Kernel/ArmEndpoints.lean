import BenzelProblem6Kernel.ArmCarriers
import BenzelProblem6Kernel.BallotWords

/-!
# Concrete simplex endpoints of the six fixed-sink arms
-/

namespace BenzelProblem6Kernel

structure IntSimplex where
  u : ℤ
  v : ℤ
  w : ℤ
  deriving DecidableEq, Repr

def intStepA (p : IntSimplex) : IntSimplex :=
  ⟨p.u - 1, p.v, p.w + 1⟩

def intStepB (p : IntSimplex) : IntSimplex :=
  ⟨p.u, p.v + 1, p.w - 1⟩

def intStepC (p : IntSimplex) : IntSimplex :=
  ⟨p.u + 1, p.v - 1, p.w⟩

def intSink (x y z : ℕ) : IntSimplex :=
  ⟨x + 1, y + 1, z + 1⟩

def labelZeroPrefixPoint (t : ℕ) (word : List BallotMove) : IntSimplex :=
  ⟨(majorityCount word : ℤ) - minorityCount word,
    (t : ℤ) - majorityCount word,
    minorityCount word⟩

def labelOnePrefixPoint (t : ℕ) (word : List BallotMove) : IntSimplex :=
  ⟨minorityCount word,
    (majorityCount word : ℤ) - minorityCount word,
    (t : ℤ) - majorityCount word⟩

def labelTwoPrefixPoint (t : ℕ) (word : List BallotMove) : IntSimplex :=
  ⟨(t : ℤ) - majorityCount word,
    minorityCount word,
    (majorityCount word : ℤ) - minorityCount word⟩

theorem positive_labelZero_endpoint (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1)) :
    intStepC (labelZeroPrefixPoint (x + y + z + 3)
      (recursiveBallotWord path)) = intSink x y z := by
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  simp [intStepC, labelZeroPrefixPoint, intSink]
  omega

theorem negative_labelZero_endpoint (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z) :
    intStepA (labelZeroPrefixPoint (x + y + z + 3)
      (recursiveBallotWord path)) = intSink x y z := by
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  simp [intStepA, labelZeroPrefixPoint, intSink]
  omega

theorem positive_labelOne_endpoint (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1)) :
    intStepB (labelOnePrefixPoint (x + y + z + 3)
      (recursiveBallotWord path)) = intSink x y z := by
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  simp [intStepB, labelOnePrefixPoint, intSink]
  omega

theorem negative_labelOne_endpoint (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x) :
    intStepC (labelOnePrefixPoint (x + y + z + 3)
      (recursiveBallotWord path)) = intSink x y z := by
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  simp [intStepC, labelOnePrefixPoint, intSink]
  omega

theorem positive_labelTwo_endpoint (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1)) :
    intStepA (labelTwoPrefixPoint (x + y + z + 3)
      (recursiveBallotWord path)) = intSink x y z := by
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  simp [intStepA, labelTwoPrefixPoint, intSink]
  omega

theorem negative_labelTwo_endpoint (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y) :
    intStepB (labelTwoPrefixPoint (x + y + z + 3)
      (recursiveBallotWord path)) = intSink x y z := by
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  simp [intStepB, labelTwoPrefixPoint, intSink]
  omega

end BenzelProblem6Kernel
