import BenzelProblem6Kernel.WordBonePlacements

/-!
# Simplex-coordinate moves induce the corresponding owner-anchor moves
-/

namespace BenzelProblem6Kernel

theorem owner_stepA_of_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hcoord : q.u + 1 = p.u ∧ q.v = p.v ∧ q.w = p.w + 1) :
    addCell (ownerQ p, ownerR p) stepA = (ownerQ q, ownerR q) := by
  apply Prod.ext <;>
    simp [ownerQ, ownerR, addCell, stepA] <;>
    omega

theorem owner_stepB_of_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hcoord : q.u = p.u ∧ q.v = p.v + 1 ∧ q.w + 1 = p.w) :
    addCell (ownerQ p, ownerR p) stepB = (ownerQ q, ownerR q) := by
  apply Prod.ext <;>
    simp [ownerQ, ownerR, addCell, stepB] <;>
    omega

theorem owner_stepC_of_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hcoord : q.u = p.u + 1 ∧ q.v + 1 = p.v ∧ q.w = p.w) :
    addCell (ownerQ p, ownerR p) stepC = (ownerQ q, ownerR q) := by
  apply Prod.ext <;>
    simp [ownerQ, ownerR, addCell, stepC] <;>
    omega

end BenzelProblem6Kernel
