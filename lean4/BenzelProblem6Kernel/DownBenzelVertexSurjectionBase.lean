import BenzelProblem6Kernel.DownBenzelVertexInjection

/-! # Boundary exclusions for down-vertex surjectivity -/

namespace BenzelProblem6Kernel

theorem downOne_sourceZero_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (downAnchorCell
        (simplexAnchor (sourceZero (m + 4))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, downAnchorCell,
      simplexAnchor, sourceZero] <;> omega

theorem downOne_sourceTwo_outside (m : ℕ) (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (downAnchorCell
        (simplexAnchor (sourceTwo (m + 4))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, downAnchorCell,
      simplexAnchor, sourceTwo] <;> omega

theorem downOne_simplex_allowed_of_anchor_mem (m : ℕ)
    (p : SimplexPoint (m + 4))
    (hmem : ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (downAnchorCell (simplexAnchor p) label)) :
    p ∉ downOneExceptions (m + 3) := by
  rintro hexception
  obtain ⟨label, hlabel⟩ := hmem
  simp only [downOneExceptions, Finset.mem_insert,
    Finset.mem_singleton] at hexception
  rcases hexception with hp | hp
  · subst p
    exact downOne_sourceZero_outside m label hlabel
  · subst p
    exact downOne_sourceTwo_outside m label hlabel

theorem downTwo_raw_w_positive (m : ℕ)
    (p : SimplexPoint (m + 5))
    (hmem : ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (downAnchorCell (simplexAnchor p) label)) :
    0 < p.w := by
  by_contra hw
  obtain ⟨label, hlabel⟩ := hmem
  have hsum := p.sum_eq
  cases label <;>
    dsimp [inPeripheralBenzel, downAnchorCell,
      simplexAnchor] at hlabel <;> omega

theorem downTwo_raw_sourceOne_outside (m : ℕ)
    (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (downAnchorCell
        (simplexAnchor (sourceOne (m + 5))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, downAnchorCell,
      simplexAnchor, sourceOne] <;> omega

theorem downTwo_raw_extra₂_outside (m : ℕ)
    (label : MicroLabel) :
    ¬inPeripheralBenzel (m + 5)
      (downAnchorCell
        (simplexAnchor (upTwoExtra₂ (m + 3))) label) := by
  cases label <;>
    simp [inPeripheralBenzel, downAnchorCell,
      simplexAnchor, upTwoExtra₂] <;> omega

end BenzelProblem6Kernel
