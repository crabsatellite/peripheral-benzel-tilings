import BenzelProblem6Kernel.DownBenzelVertexSurjectionBase

/-! # Shift each down-vertex residue to one common simplex level -/

namespace BenzelProblem6Kernel

theorem downZero_anchor_has_parameter (m : ℕ)
    (anchor : Cell) (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5)
      (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (m + 3) anchor) :
    ∃ p : SimplexPoint (m + 4),
      downZeroSimplexAnchor p = anchor := by
  rcases anchor with ⟨q, r⟩
  let shifted : Cell := (q - 1, r + 1)
  have hphaseLinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphaseLinear
  obtain ⟨phaseK, hphaseK⟩ := hphaseLinear
  have hshiftPhase : IsOwnerPhase (m + 4) shifted := by
    rw [IsOwnerPhase, Int.modEq_iff_dvd,
      Int.dvd_iff_emod_eq_zero] at hphase ⊢
    dsimp [shifted]
    push_cast
    omega
  have hshiftMem : inPeripheralBenzel (m + 6)
      (cellForOwnerAnchor shifted .zero) := by
    cases label <;>
      dsimp [inPeripheralBenzel, downAnchorCell,
        cellForOwnerAnchor, shifted] at hmem ⊢ <;> omega
  have hn : 5 ≤ m + 6 := by omega
  have hphase' : IsOwnerPhase (m + 6 - 2) shifted := by
    simpa [show m + 6 - 2 = m + 4 by omega] using hshiftPhase
  obtain ⟨p, hq, hr⟩ :=
    phase_anchor_has_simplex hn shifted .zero hphase' hshiftMem
  let p' : SimplexPoint (m + 4) :=
    { u := p.u
      v := p.v
      w := p.w
      sum_eq := by
        have hsum := p.sum_eq
        omega }
  refine ⟨p', ?_⟩
  apply Prod.ext
  · dsimp [p', downZeroSimplexAnchor]
    have hq' := hq
    dsimp [ownerQ, shifted] at hq'
    omega
  · dsimp [p', downZeroSimplexAnchor]
    have hr' := hr
    dsimp [ownerR, shifted] at hr'
    omega

theorem downOne_anchor_has_parameter (m : ℕ)
    (anchor : Cell) (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5)
      (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (m + 4) anchor) :
    ∃ p : SimplexPoint (m + 4),
      downOneSimplexAnchor p = anchor := by
  have hphaseLinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphaseLinear
  obtain ⟨phaseK, hphaseK⟩ := hphaseLinear
  have hanchorMem : inPeripheralBenzel (m + 6)
      (cellForOwnerAnchor anchor .zero) := by
    rcases anchor with ⟨q, r⟩
    cases label <;>
      dsimp [inPeripheralBenzel, downAnchorCell,
        cellForOwnerAnchor] at hmem ⊢ <;> omega
  have hn : 5 ≤ m + 6 := by omega
  have hphase' : IsOwnerPhase (m + 6 - 2) anchor := by
    simpa [show m + 6 - 2 = m + 4 by omega] using hphase
  obtain ⟨p, hq, hr⟩ :=
    phase_anchor_has_simplex hn anchor .zero hphase' hanchorMem
  let p' : SimplexPoint (m + 4) :=
    { u := p.u
      v := p.v
      w := p.w
      sum_eq := by
        have hsum := p.sum_eq
        omega }
  refine ⟨p', ?_⟩
  apply Prod.ext
  · simpa [p', downOneSimplexAnchor, simplexAnchor, ownerQ] using hq
  · simpa [p', downOneSimplexAnchor, simplexAnchor, ownerR] using hr

theorem downTwo_anchor_has_parameter (m : ℕ)
    (anchor : Cell) (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5)
      (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (m + 5) anchor) :
    ∃ p : SimplexPoint (m + 4),
      downTwoSimplexAnchor p = anchor := by
  rcases anchor with ⟨q, r⟩
  let shifted : Cell := (q - 1, r)
  have hphaseLinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphaseLinear
  obtain ⟨phaseK, hphaseK⟩ := hphaseLinear
  have hshiftPhase : IsOwnerPhase (m + 4) shifted := by
    rw [IsOwnerPhase, Int.modEq_iff_dvd,
      Int.dvd_iff_emod_eq_zero] at hphase ⊢
    dsimp [shifted]
    push_cast
    omega
  have hshiftMem : inPeripheralBenzel (m + 6)
      (cellForOwnerAnchor shifted .one) := by
    cases label <;>
      dsimp [inPeripheralBenzel, downAnchorCell,
        cellForOwnerAnchor, shifted] at hmem ⊢ <;> omega
  have hn : 5 ≤ m + 6 := by omega
  have hphase' : IsOwnerPhase (m + 6 - 2) shifted := by
    simpa [show m + 6 - 2 = m + 4 by omega] using hshiftPhase
  obtain ⟨p, hq, hr⟩ :=
    phase_anchor_has_simplex hn shifted .one hphase' hshiftMem
  let p' : SimplexPoint (m + 4) :=
    { u := p.u
      v := p.v
      w := p.w
      sum_eq := by
        have hsum := p.sum_eq
        omega }
  refine ⟨p', ?_⟩
  apply Prod.ext
  · dsimp [p', downTwoSimplexAnchor]
    have hq' := hq
    dsimp [ownerQ, shifted] at hq'
    omega
  · dsimp [p', downTwoSimplexAnchor]
    have hr' := hr
    dsimp [ownerR, shifted] at hr'
    omega

end BenzelProblem6Kernel
