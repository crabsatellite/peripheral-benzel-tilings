import BenzelProblem6Kernel.Basic

/-!
# Owner-label energy identities

This file contains the arithmetic producer behind the local energy table.  The
literal classification of translated prototiles into one-, two-, and
three-owner cases is intentionally kept in a later file.
-/

namespace BenzelProblem6Kernel

def otherLabelEnergy : MicroLabel → ℤ → ℤ → ℤ
  | .zero, q, r => ownerPotential .one q r + ownerPotential .two q r
  | .one, q, r => ownerPotential .zero q r + ownerPotential .two q r
  | .two, q, r => ownerPotential .zero q r + ownerPotential .one q r

theorem otherLabelEnergy_eq_neg (label : MicroLabel) (q r : ℤ) :
    otherLabelEnergy label q r = -ownerPotential label q r := by
  rcases label with _ | _ | _
  all_goals simp [otherLabelEnergy, ownerPotential] <;> omega

theorem twoOwnerBone_energy_one
    (label : MicroLabel) (q r q' r' : ℤ)
    (hstep : ownerPotential label q' r' = ownerPotential label q r + 1) :
    otherLabelEnergy label q r + ownerPotential label q' r' = 1 := by
  rw [otherLabelEnergy_eq_neg, hstep]
  omega

theorem allowedTwoOwnerBone_energy_one
    (label : MicroLabel) (q r dq dr : ℤ)
    (h : allowedStep label (dq, dr)) :
    otherLabelEnergy label q r +
        ownerPotential label (q + dq) (r + dr) = 1 := by
  apply twoOwnerBone_energy_one
  exact allowedStep_potential_increase label q r dq dr h

theorem bad_tile_counts_zero
    (bones wrongPhaseStones threeOwnerBones : ℕ)
    (henergy :
      (bones : ℤ) + 3 * ((wrongPhaseStones : ℤ) + threeOwnerBones) = bones) :
    wrongPhaseStones = 0 ∧ threeOwnerBones = 0 := by
  omega

end BenzelProblem6Kernel
