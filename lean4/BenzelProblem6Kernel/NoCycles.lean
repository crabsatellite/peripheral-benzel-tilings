import BenzelProblem6Kernel.Basic

/-!
# Strict label potentials exclude directed cycles
-/

namespace BenzelProblem6Kernel

def addCell (a b : Cell) : Cell := (a.1 + b.1, a.2 + b.2)

def walkEnd : Cell → List Cell → Cell
  | start, [] => start
  | start, step :: steps => walkEnd (addCell start step) steps

theorem walk_potential_increase
    (label : MicroLabel) (start : Cell) (steps : List Cell)
    (hallowed : ∀ step ∈ steps, allowedStep label step) :
    ownerPotential label (walkEnd start steps).1 (walkEnd start steps).2 =
      ownerPotential label start.1 start.2 + steps.length := by
  induction steps generalizing start with
  | nil => simp [walkEnd]
  | cons step steps ih =>
      have hstep : allowedStep label step := hallowed step (by simp)
      have htail : ∀ d ∈ steps, allowedStep label d := by
        intro d hd
        exact hallowed d (by simp [hd])
      rw [walkEnd, ih (addCell start step) htail]
      rw [show ownerPotential label (addCell start step).1 (addCell start step).2 =
          ownerPotential label start.1 start.2 + 1 by
        simpa [addCell] using allowedStep_potential_increase label
          start.1 start.2 step.1 step.2 hstep]
      simp
      omega

theorem allowed_walk_closed_iff_empty
    (label : MicroLabel) (start : Cell) (steps : List Cell)
    (hallowed : ∀ step ∈ steps, allowedStep label step)
    (hclosed : walkEnd start steps = start) :
    steps = [] := by
  have hpot := walk_potential_increase label start steps hallowed
  rw [hclosed] at hpot
  have hlen : steps.length = 0 := by omega
  exact List.length_eq_zero.mp hlen

end BenzelProblem6Kernel
