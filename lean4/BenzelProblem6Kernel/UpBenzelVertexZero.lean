import BenzelProblem6Kernel.BenzelVertexAnchors

/-! # Residue-zero up-vertex parameters -/

namespace BenzelProblem6Kernel

theorem upZeroParameter_anchor_mem (m : ℕ)
    (p : SimplexPoint (m + 3)) :
    ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (cellForOwnerAnchor (simplexAnchor p) label) := by
  have hn : 5 ≤ m + 5 := by omega
  have hsum := p.sum_eq
  by_cases hv : p.v < m + 3
  · refine ⟨.zero, ?_⟩
    simpa [simplexAnchor] using (owner_zero_mem_iff hn p).mpr hv
  · by_cases hw : p.w < m + 3
    · refine ⟨.one, ?_⟩
      simpa [simplexAnchor] using (owner_one_mem_iff hn p).mpr hw
    · have hu : p.u < m + 3 := by omega
      refine ⟨.two, ?_⟩
      simpa [simplexAnchor] using (owner_two_mem_iff hn p).mpr hu

end BenzelProblem6Kernel
