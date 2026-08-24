import BenzelProblem6Kernel.UpBenzelVertexZero

/-! # Residue-one up-vertex parameters -/

namespace BenzelProblem6Kernel

theorem upOneParameter_bounds {t : ℕ}
    (p : UpOneParameter t) :
    p.1.u ≤ t ∧ p.1.v ≤ t ∧ p.1.w ≤ t := by
  have hsum := p.1.sum_eq
  constructor
  · by_contra hu
    apply p.2
    have hp : p.1 = sourceTwo (t + 1) := by
      apply simplexPoint_ext <;> simp [sourceTwo] <;> omega
    simp [upOneExceptions, hp]
  · constructor
    · by_contra hv
      apply p.2
      have hp : p.1 = sourceZero (t + 1) := by
        apply simplexPoint_ext <;> simp [sourceZero] <;> omega
      simp [upOneExceptions, hp]
    · by_contra hw
      apply p.2
      have hp : p.1 = sourceOne (t + 1) := by
        apply simplexPoint_ext <;> simp [sourceOne] <;> omega
      simp [upOneExceptions, hp]

theorem upOneParameter_anchor_mem (m : ℕ)
    (p : UpOneParameter (m + 3)) :
    ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (cellForOwnerAnchor (simplexAnchor p.1) label) := by
  have hsum := p.1.sum_eq
  have hbounds := upOneParameter_bounds p
  by_cases hu : 0 < p.1.u
  · refine ⟨.one, ?_⟩
    dsimp [inPeripheralBenzel, cellForOwnerAnchor, simplexAnchor]
    omega
  · by_cases hv : 0 < p.1.v
    · refine ⟨.two, ?_⟩
      dsimp [inPeripheralBenzel, cellForOwnerAnchor, simplexAnchor]
      omega
    · have hw : 0 < p.1.w := by omega
      refine ⟨.zero, ?_⟩
      dsimp [inPeripheralBenzel, cellForOwnerAnchor, simplexAnchor]
      omega

end BenzelProblem6Kernel
