import Mathlib.Data.Int.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Basic finite labels and owner coordinates
-/

namespace BenzelProblem6Kernel

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

@[simp] theorem ownerPotential_zero (q r : ℤ) :
    ownerPotential .zero q r = q + r := rfl

@[simp] theorem ownerPotential_one (q r : ℤ) :
    ownerPotential .one q r = -q := rfl

@[simp] theorem ownerPotential_two (q r : ℤ) :
    ownerPotential .two q r = -r := rfl

theorem ownerPotential_sum (q r : ℤ) :
    ownerPotential .zero q r + ownerPotential .one q r +
        ownerPotential .two q r = 0 := by
  simp [ownerPotential]

def stepA : Cell := (2, -1)
def stepB : Cell := (-1, -1)
def stepC : Cell := (-1, 2)

def allowedStep : MicroLabel → Cell → Prop
  | .zero, d => d = stepA ∨ d = stepC
  | .one, d => d = stepB ∨ d = stepC
  | .two, d => d = stepA ∨ d = stepB

theorem allowedStep_potential_increase
    (label : MicroLabel) (q r dq dr : ℤ)
    (h : allowedStep label (dq, dr)) :
    ownerPotential label (q + dq) (r + dr) =
      ownerPotential label q r + 1 := by
  rcases label with _ | _ | _ <;>
    simp only [allowedStep] at h <;>
    rcases h with h | h <;>
    simp only [stepA, stepB, stepC, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    simp [ownerPotential] <;>
    omega

end BenzelProblem6Kernel
