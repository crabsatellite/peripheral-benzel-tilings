import BenzelProblem6Kernel.UpBenzelVertexOne

/-! # Residue-two up-vertex parameters -/

namespace BenzelProblem6Kernel

theorem upTwo_not_sourceOne {t : ℕ}
    (p : UpTwoParameter t) : p.1 ≠ sourceOne (t + 2) := by
  intro hp
  apply p.2
  simp [upTwoExceptions, hp]

theorem upTwo_not_sourceZero {t : ℕ}
    (p : UpTwoParameter t) : p.1 ≠ sourceZero (t + 2) := by
  intro hp
  apply p.2
  simp [upTwoExceptions, hp]

theorem upTwo_not_extra₀ {t : ℕ}
    (p : UpTwoParameter t) : p.1 ≠ upTwoExtra₀ t := by
  intro hp
  apply p.2
  simp [upTwoExceptions, hp]

theorem upTwo_not_sourceTwo {t : ℕ}
    (p : UpTwoParameter t) : p.1 ≠ sourceTwo (t + 2) := by
  intro hp
  apply p.2
  simp [upTwoExceptions, hp]

theorem upTwo_not_extra₂ {t : ℕ}
    (p : UpTwoParameter t) : p.1 ≠ upTwoExtra₂ t := by
  intro hp
  apply p.2
  simp [upTwoExceptions, hp]

theorem upTwo_not_extra₁ {t : ℕ}
    (p : UpTwoParameter t) : p.1 ≠ upTwoExtra₁ t := by
  intro hp
  apply p.2
  simp [upTwoExceptions, hp]

theorem upTwoParameter_anchor_mem (m : ℕ)
    (p : UpTwoParameter (m + 3)) :
    ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (cellForOwnerAnchor (simplexAnchor p.1) label) := by
  have hsum := p.1.sum_eq
  by_cases hu : p.1.u = 0
  · by_cases hv : p.1.v = 0
    · exfalso
      apply upTwo_not_sourceOne p
      apply simplexPoint_ext <;> simp [sourceOne] <;> omega
    · by_cases hw : p.1.w = 0
      · exfalso
        apply upTwo_not_sourceZero p
        apply simplexPoint_ext <;> simp [sourceZero] <;> omega
      · have hwle : p.1.w ≤ m + 3 := by
          by_contra hlarge
          apply upTwo_not_extra₀ p
          apply simplexPoint_ext <;> simp [upTwoExtra₀] <;> omega
        refine ⟨.two, ?_⟩
        dsimp [inPeripheralBenzel, cellForOwnerAnchor, simplexAnchor]
        omega
  · by_cases hv : p.1.v = 0
    · have hule : p.1.u ≤ m + 3 := by
        by_contra hlarge
        by_cases hw : p.1.w = 0
        · apply upTwo_not_sourceTwo p
          apply simplexPoint_ext <;> simp [sourceTwo] <;> omega
        · apply upTwo_not_extra₂ p
          apply simplexPoint_ext <;> simp [upTwoExtra₂] <;> omega
      refine ⟨.zero, ?_⟩
      dsimp [inPeripheralBenzel, cellForOwnerAnchor, simplexAnchor]
      omega
    · have hvle : p.1.v ≤ m + 3 := by
        by_contra hlarge
        apply upTwo_not_extra₁ p
        apply simplexPoint_ext <;> simp [upTwoExtra₁] <;> omega
      refine ⟨.one, ?_⟩
      dsimp [inPeripheralBenzel, cellForOwnerAnchor, simplexAnchor]
      omega

end BenzelProblem6Kernel
