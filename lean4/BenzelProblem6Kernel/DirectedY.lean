import BenzelProblem6Kernel.OwnerEnergy
import Mathlib.Tactic.Ring

/-!
# Simplex coordinates and directed steps
-/

namespace BenzelProblem6Kernel

structure SimplexPoint (t : ℕ) where
  u : ℕ
  v : ℕ
  w : ℕ
  sum_eq : u + v + w = t
  deriving DecidableEq, Repr

def sinkPoint (x y z : ℕ) : SimplexPoint (x + y + z + 3) where
  u := x + 1
  v := y + 1
  w := z + 1
  sum_eq := by omega

theorem sinkPoint_positive (x y z : ℕ) :
    0 < (sinkPoint x y z).u ∧
    0 < (sinkPoint x y z).v ∧
    0 < (sinkPoint x y z).w := by
  simp [sinkPoint]

def sourceZero (t : ℕ) : SimplexPoint t where
  u := 0
  v := t
  w := 0
  sum_eq := by omega

def sourceOne (t : ℕ) : SimplexPoint t where
  u := 0
  v := 0
  w := t
  sum_eq := by omega

def sourceTwo (t : ℕ) : SimplexPoint t where
  u := t
  v := 0
  w := 0
  sum_eq := by omega

theorem active_owner_count_twice_identity (n : ℤ) :
    n * (n - 1) - (n - 5) * (n - 2) = 2 * (3 * (n - 2) + 1) := by
  ring

end BenzelProblem6Kernel
