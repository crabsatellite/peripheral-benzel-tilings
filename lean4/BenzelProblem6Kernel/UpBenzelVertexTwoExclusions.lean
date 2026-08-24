import BenzelProblem6Kernel.UpBenzelVertexSurjectionBase

/-! # The six excluded residue-two up-vertex parameters -/

namespace BenzelProblem6Kernel

theorem upTwo_sourceZero_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (simplexAnchor (sourceZero (m + 5))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, cellForOwnerAnchor,
      simplexAnchor, sourceZero] <;> omega

theorem upTwo_sourceOne_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (simplexAnchor (sourceOne (m + 5))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, cellForOwnerAnchor,
      simplexAnchor, sourceOne] <;> omega

theorem upTwo_sourceTwo_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (simplexAnchor (sourceTwo (m + 5))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, cellForOwnerAnchor,
      simplexAnchor, sourceTwo] <;> omega

theorem upTwo_extra₀_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (simplexAnchor (upTwoExtra₀ (m + 3))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, cellForOwnerAnchor,
      simplexAnchor, upTwoExtra₀] <;> omega

theorem upTwo_extra₁_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (simplexAnchor (upTwoExtra₁ (m + 3))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, cellForOwnerAnchor,
      simplexAnchor, upTwoExtra₁] <;> omega

theorem upTwo_extra₂_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor
        (simplexAnchor (upTwoExtra₂ (m + 3))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, cellForOwnerAnchor,
      simplexAnchor, upTwoExtra₂] <;> omega

theorem upTwo_simplex_allowed_of_anchor_mem (m : ℕ)
    (p : SimplexPoint (m + 5))
    (hmem : ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (cellForOwnerAnchor (simplexAnchor p) label)) :
    p ∉ upTwoExceptions (m + 3) := by
  rintro hexception
  obtain ⟨label, hlabel⟩ := hmem
  simp only [upTwoExceptions, Finset.mem_insert,
    Finset.mem_singleton] at hexception
  rcases hexception with hp | hp | hp | hp | hp | hp
  · subst p
    exact upTwo_sourceZero_outside m label hlabel
  · subst p
    exact upTwo_sourceOne_outside m label hlabel
  · subst p
    exact upTwo_sourceTwo_outside m label hlabel
  · subst p
    exact upTwo_extra₀_outside m label hlabel
  · subst p
    exact upTwo_extra₁_outside m label hlabel
  · subst p
    exact upTwo_extra₂_outside m label hlabel

end BenzelProblem6Kernel
