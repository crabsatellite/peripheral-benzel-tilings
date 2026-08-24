import BenzelProblem6Kernel.OwnerCoordinates
import Mathlib.Tactic.Ring

/-!
# Corner-owner and global energy arithmetic
-/

namespace BenzelProblem6Kernel

theorem cornerZero_present_energy (t : ℕ) :
    otherLabelEnergy .zero (ownerQ (sourceZero t)) (ownerR (sourceZero t)) = t := by
  simp [sourceZero, ownerQ, ownerR, otherLabelEnergy, ownerPotential]

theorem cornerOne_present_energy (t : ℕ) :
    otherLabelEnergy .one (ownerQ (sourceOne t)) (ownerR (sourceOne t)) = t := by
  simp [sourceOne, ownerQ, ownerR, otherLabelEnergy, ownerPotential]

theorem cornerTwo_present_energy (t : ℕ) :
    otherLabelEnergy .two (ownerQ (sourceTwo t)) (ownerR (sourceTwo t)) = t := by
  simp [sourceTwo, ownerQ, ownerR, otherLabelEnergy, ownerPotential]

theorem three_corner_energy (t : ℕ) :
    otherLabelEnergy .zero (ownerQ (sourceZero t)) (ownerR (sourceZero t)) +
      otherLabelEnergy .one (ownerQ (sourceOne t)) (ownerR (sourceOne t)) +
      otherLabelEnergy .two (ownerQ (sourceTwo t)) (ownerR (sourceTwo t)) =
        3 * t := by
  rw [cornerZero_present_energy, cornerOne_present_energy, cornerTwo_present_energy]
  omega

theorem bone_count_twice_identity (n : ℤ) :
    (n - 2) * (n + 1) - (n - 5) * (n - 2) = 2 * (3 * (n - 2)) := by
  ring

end BenzelProblem6Kernel
