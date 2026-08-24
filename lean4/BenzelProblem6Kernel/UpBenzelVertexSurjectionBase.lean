import BenzelProblem6Kernel.UpBenzelVertexInjection

/-! # Phase-to-simplex transport for up-vertex surjectivity -/

namespace BenzelProblem6Kernel

theorem upAnchor_has_simplex_at_phase (m s : ℕ)
    (anchor : Cell) (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5)
      (cellForOwnerAnchor anchor label))
    (hphase : IsOwnerPhase (m + 3 + s) anchor) :
    ∃ p : SimplexPoint (m + 3 + s), simplexAnchor p = anchor := by
  have hmono : m + 5 ≤ m + 5 + s := by omega
  have hmem' : inPeripheralBenzel (m + 5 + s)
      (cellForOwnerAnchor anchor label) :=
    inPeripheralBenzel_mono hmono hmem
  have hn : 5 ≤ m + 5 + s := by omega
  have hphase' : IsOwnerPhase (m + 5 + s - 2) anchor := by
    simpa [show m + 5 + s - 2 = m + 3 + s by omega] using hphase
  obtain ⟨raw, hq, hr⟩ :=
    phase_anchor_has_simplex hn anchor label hphase' hmem'
  let p : SimplexPoint (m + 3 + s) :=
    { u := raw.u
      v := raw.v
      w := raw.w
      sum_eq := by
        have hsum := raw.sum_eq
        omega }
  refine ⟨p, ?_⟩
  apply Prod.ext
  · simpa [p, simplexAnchor, ownerQ] using hq
  · simpa [p, simplexAnchor, ownerR] using hr

theorem upOne_simplex_allowed_of_anchor_mem (m : ℕ)
    (p : SimplexPoint (m + 4))
    (hmem : ∃ label : MicroLabel,
      inPeripheralBenzel (m + 5)
        (cellForOwnerAnchor (simplexAnchor p) label)) :
    p ∉ upOneExceptions (m + 3) := by
  rintro hexception
  obtain ⟨label, hlabel⟩ := hmem
  simp only [upOneExceptions, Finset.mem_insert,
    Finset.mem_singleton] at hexception
  rcases hexception with hp | hp | hp
  · subst p
    cases label <;>
      simp [inPeripheralBenzel, cellForOwnerAnchor,
        simplexAnchor, sourceZero] at hlabel <;> omega
  · subst p
    cases label <;>
      simp [inPeripheralBenzel, cellForOwnerAnchor,
        simplexAnchor, sourceOne] at hlabel <;> omega
  · subst p
    cases label <;>
      simp [inPeripheralBenzel, cellForOwnerAnchor,
        simplexAnchor, sourceTwo] at hlabel <;> omega

end BenzelProblem6Kernel
