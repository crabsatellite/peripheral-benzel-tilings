import Mathlib.Data.Nat.Choose.Cast
import Lean.Elab.Tactic.Omega

/-! # Basic owner coordinates for the finite-defect hierarchy -/

namespace FiniteDefects

abbrev Cell := ℤ × ℤ

inductive MicroLabel
  | zero
  | one
  | two
  deriving DecidableEq, Repr

def ownerPotential : MicroLabel → ℤ → ℤ → ℤ
  | .zero, q, r => q + r
  | .one, q, _ => -q
  | .two, _, r => -r

theorem ownerPotential_sum (q r : ℤ) :
    ownerPotential .zero q r + ownerPotential .one q r +
        ownerPotential .two q r = 0 := by
  simp [ownerPotential]

structure SimplexPoint (t : ℕ) where
  u : ℕ
  v : ℕ
  w : ℕ
  sum_eq : u + v + w = t
  deriving DecidableEq, Repr

theorem simplexPoint_ext {t : ℕ} {p q : SimplexPoint t}
    (hu : p.u = q.u) (hv : p.v = q.v) (hw : p.w = q.w) : p = q := by
  cases p
  cases q
  simp_all

def ownerQ {t : ℕ} (p : SimplexPoint t) : ℤ := (p.w : ℤ) - p.u
def ownerR {t : ℕ} (p : SimplexPoint t) : ℤ := (p.u : ℤ) - p.v

theorem owner_phase_identity {t : ℕ} (p : SimplexPoint t) :
    ownerQ p - ownerR p = (t : ℤ) - 3 * p.u := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

end FiniteDefects
