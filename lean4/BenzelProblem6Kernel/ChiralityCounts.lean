import BenzelProblem6Kernel.DirectedY
import Mathlib.Data.Nat.Choose.Basic

/-!
# Fixed-sink chirality products
-/

namespace BenzelProblem6Kernel

def ballotNumber (total : ℕ) : ℕ → ℕ
  | 0 => 1
  | down + 1 => total.choose (down + 1) - total.choose down

def positiveChiralityCount (x y z : ℕ) : ℕ :=
  (2 * x + y + 2).choose x *
  (2 * y + z + 2).choose y *
  (2 * z + x + 2).choose z

def negativeChiralityCount (x y z : ℕ) : ℕ :=
  ballotNumber (2 * x + y + 2) x *
  ballotNumber (2 * y + z + 2) y *
  ballotNumber (2 * z + x + 2) z

def fixedSinkCount (x y z : ℕ) : ℕ :=
  positiveChiralityCount x y z + negativeChiralityCount x y z

@[simp] theorem positiveChiralityCount_zero :
    positiveChiralityCount 0 0 0 = 1 := by
  decide

@[simp] theorem negativeChiralityCount_zero :
    negativeChiralityCount 0 0 0 = 1 := by
  decide

@[simp] theorem fixedSinkCount_zero : fixedSinkCount 0 0 0 = 2 := by
  decide

end BenzelProblem6Kernel
