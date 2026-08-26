import D4KernelOnly.GeneralClassZeroDownVertexCount

/-! # Surjectivity of the class-zero down-vertex parameters -/

namespace FiniteDefects

open BenzelProblem6Kernel

def czDownPhase0LiftLabel : BenzelProblem6Kernel.MicroLabel → MicroLabel
  | .zero => .one
  | .one => .one
  | .two => .zero

def czDownPhase1LiftLabel : BenzelProblem6Kernel.MicroLabel → MicroLabel
  | .zero => .zero
  | .one => .two
  | .two => .zero

def czDownPhase2LiftLabel : BenzelProblem6Kernel.MicroLabel → MicroLabel
  | .zero => .one
  | .one => .two
  | .two => .two

theorem czDownPhase0_anchor_has_parameter
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (anchor : Cell) (label : BenzelProblem6Kernel.MicroLabel)
    (hmem : inBenzel (2 * s + r) (s + 2 * r) (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (2 * s + r - 2) anchor) :
    ∃ p : SimplexPoint (2 * s + r - 1), czDownPhase0Anchor p = anchor := by
  rcases anchor with ⟨q, z⟩
  let shifted : Cell := (q - 1, z + 1)
  have hlinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hlinear
  obtain ⟨phaseK, hphaseK⟩ := hlinear
  have hshiftPhase : IsOwnerPhase (2 * s + r - 1) shifted := by
    rw [IsOwnerPhase, Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
      at hphase ⊢
    dsimp [shifted]
    omega
  have hshiftMem : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
      (cellForOwnerAnchor shifted (czDownPhase0LiftLabel label)) := by
    cases label <;>
      dsimp [inBenzel, downAnchorCell, cellForOwnerAnchor,
        czDownPhase0LiftLabel, shifted]
        at hmem ⊢ <;> omega
  have ht : 2 * s + r - 1 + 2 = 2 * s + r + 1 := by omega
  rw [← ht] at hshiftMem
  obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
    (2 * s + r - 1) (s + 2 * r + 1) shifted
      (czDownPhase0LiftLabel label) hshiftPhase hshiftMem
  refine ⟨p, Prod.ext ?_ ?_⟩
  · dsimp [czDownPhase0Anchor, shifted] at hq ⊢; omega
  · dsimp [czDownPhase0Anchor, shifted] at hz ⊢; omega

theorem czDownPhase1_anchor_has_parameter
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (anchor : Cell) (label : BenzelProblem6Kernel.MicroLabel)
    (hmem : inBenzel (2 * s + r) (s + 2 * r) (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (2 * s + r - 1) anchor) :
    ∃ p : SimplexPoint (2 * s + r - 1), czDownPhase1Anchor p = anchor := by
  have hlinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hlinear
  obtain ⟨phaseK, hphaseK⟩ := hlinear
  have hanchorMem : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
      (cellForOwnerAnchor anchor (czDownPhase1LiftLabel label)) := by
    rcases anchor with ⟨q, z⟩
    cases label <;>
      dsimp [inBenzel, downAnchorCell, cellForOwnerAnchor,
        czDownPhase1LiftLabel] at hmem ⊢ <;> omega
  have ht : 2 * s + r - 1 + 2 = 2 * s + r + 1 := by omega
  rw [← ht] at hanchorMem
  obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
    (2 * s + r - 1) (s + 2 * r + 1) anchor
      (czDownPhase1LiftLabel label) hphase hanchorMem
  exact ⟨p, Prod.ext hq hz⟩

theorem czDownPhase2_anchor_has_parameter
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (anchor : Cell) (label : BenzelProblem6Kernel.MicroLabel)
    (hmem : inBenzel (2 * s + r) (s + 2 * r) (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (2 * s + r) anchor) :
    ∃ p : SimplexPoint (2 * s + r - 1), czDownPhase2Anchor p = anchor := by
  rcases anchor with ⟨q, z⟩
  let shifted : Cell := (q - 1, z)
  have hlinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hlinear
  obtain ⟨phaseK, hphaseK⟩ := hlinear
  have hshiftPhase : IsOwnerPhase (2 * s + r - 1) shifted := by
    rw [IsOwnerPhase, Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
      at hphase ⊢
    dsimp [shifted]
    omega
  have hshiftMem : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
      (cellForOwnerAnchor shifted (czDownPhase2LiftLabel label)) := by
    cases label <;>
      dsimp [inBenzel, downAnchorCell, cellForOwnerAnchor,
        czDownPhase2LiftLabel, shifted]
        at hmem ⊢ <;> omega
  have ht : 2 * s + r - 1 + 2 = 2 * s + r + 1 := by omega
  rw [← ht] at hshiftMem
  obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
    (2 * s + r - 1) (s + 2 * r + 1) shifted
      (czDownPhase2LiftLabel label) hshiftPhase hshiftMem
  refine ⟨p, Prod.ext ?_ ?_⟩
  · dsimp [czDownPhase2Anchor, shifted] at hq ⊢; omega
  · dsimp [czDownPhase2Anchor, shifted] at hz ⊢; omega

theorem czDownParameterToAnchor_surjective
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Function.Surjective (czDownParameterToAnchor s r hs hr) := by
  intro anchor
  obtain ⟨label, hmem⟩ := (mem_offsetDownAnchorFinset_iff
    (2 * s + r - 2) (3 * s) anchor.1).1 anchor.2
  have hp := classZeroOffsetParameters s r hs hr
  rw [hp.1, hp.2] at hmem
  obtain ⟨c, hphase⟩ := cmo_exists_anchor_phase_offset (2 * s + r - 2) anchor.1
  rcases c with ⟨c, hc⟩
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hcases with hcase | hcase | hcase
  · subst c
    obtain ⟨p, hanchor⟩ :=
      czDownPhase0_anchor_has_parameter s r hs hr anchor.1 label hmem hphase
    have hb := (czDownPhase0_mem_iff s r hs hr p).1 ⟨label, by rwa [hanchor]⟩
    exact ⟨.phase0 ⟨⟨p, hb.1⟩, hb.2⟩, Subtype.ext hanchor⟩
  · subst c
    have ht : 2 * s + r - 2 + 1 = 2 * s + r - 1 := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase; rw [ht] at hphase
    obtain ⟨p, hanchor⟩ :=
      czDownPhase1_anchor_has_parameter s r hs hr anchor.1 label hmem hphase
    have hb := (czDownPhase1_mem_iff s r hs hr p).1 ⟨label, by rwa [hanchor]⟩
    exact ⟨.phase1 ⟨⟨p, hb.1⟩, hb.2⟩, Subtype.ext hanchor⟩
  · subst c
    have ht : 2 * s + r - 2 + 2 = 2 * s + r := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase; rw [ht] at hphase
    obtain ⟨p, hanchor⟩ :=
      czDownPhase2_anchor_has_parameter s r hs hr anchor.1 label hmem hphase
    have hb := (czDownPhase2_mem_iff s r hs hr p).1 ⟨label, by rwa [hanchor]⟩
    exact ⟨.phase2 ⟨⟨p, hb.1⟩, hb.2⟩, Subtype.ext hanchor⟩

end FiniteDefects
