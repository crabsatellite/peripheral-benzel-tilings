import BenzelProblem6Kernel.DirectedY
import Mathlib.Tactic.Ring

/-!
# Inverse owner/simplex coordinate algebra
-/

namespace BenzelProblem6Kernel

def ownerQ {t : ℕ} (p : SimplexPoint t) : ℤ := (p.w : ℤ) - p.u
def ownerR {t : ℕ} (p : SimplexPoint t) : ℤ := (p.u : ℤ) - p.v

theorem owner_phase_identity {t : ℕ} (p : SimplexPoint t) :
    ownerQ p - ownerR p = (t : ℤ) - 3 * p.u := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

theorem recover_u_numerator {t : ℕ} (p : SimplexPoint t) :
    (t : ℤ) - ownerQ p + ownerR p = 3 * p.u := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

theorem recover_v_numerator {t : ℕ} (p : SimplexPoint t) :
    (t : ℤ) - ownerQ p - 2 * ownerR p = 3 * p.v := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

theorem recover_w_numerator {t : ℕ} (p : SimplexPoint t) :
    (t : ℤ) + 2 * ownerQ p + ownerR p = 3 * p.w := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

end BenzelProblem6Kernel
