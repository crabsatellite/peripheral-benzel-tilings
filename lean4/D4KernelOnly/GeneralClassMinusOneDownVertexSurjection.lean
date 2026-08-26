import D4KernelOnly.GeneralClassMinusOneDownVertexCount

/-! # Surjectivity of the class-minus-one down-vertex parameters -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem cmoDownPhase0_anchor_has_parameter
    (s r : ℕ) (hs : 1 ≤ s) (anchor : Cell)
    (label : BenzelProblem6Kernel.MicroLabel)
    (hmem : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
      (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (2 * s + r - 1) anchor) :
    ∃ p : SimplexPoint (2 * s + r), cmoDownPhase0Anchor p = anchor := by
  rcases anchor with ⟨q, z⟩
  let shifted : Cell := (q - 1, z + 1)
  have hphaseLinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphaseLinear
  obtain ⟨phaseK, hphaseK⟩ := hphaseLinear
  have hshiftPhase : IsOwnerPhase (2 * s + r) shifted := by
    rw [IsOwnerPhase, Int.modEq_iff_dvd,
      Int.dvd_iff_emod_eq_zero] at hphase ⊢
    dsimp [shifted]
    push_cast
    omega
  have hshiftMem : inBenzel (2 * s + r + 2) (s + 2 * r + 2)
      (cellForOwnerAnchor shifted .zero) := by
    cases label <;>
      dsimp [inBenzel, downAnchorCell, cellForOwnerAnchor, shifted]
        at hmem ⊢ <;> omega
  obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
    (2 * s + r) (s + 2 * r + 2) shifted .zero hshiftPhase hshiftMem
  refine ⟨p, Prod.ext ?_ ?_⟩
  · dsimp [cmoDownPhase0Anchor, shifted] at hq ⊢
    omega
  · dsimp [cmoDownPhase0Anchor, shifted] at hz ⊢
    omega

theorem cmoDownPhase1_anchor_has_parameter
    (s r : ℕ) (anchor : Cell)
    (label : BenzelProblem6Kernel.MicroLabel)
    (hmem : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
      (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (2 * s + r) anchor) :
    ∃ p : SimplexPoint (2 * s + r), cmoDownPhase1Anchor p = anchor := by
  have hphaseLinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphaseLinear
  obtain ⟨phaseK, hphaseK⟩ := hphaseLinear
  have hanchorMem : inBenzel (2 * s + r + 2) (s + 2 * r + 2)
      (cellForOwnerAnchor anchor .zero) := by
    rcases anchor with ⟨q, z⟩
    cases label <;>
      dsimp [inBenzel, downAnchorCell, cellForOwnerAnchor] at hmem ⊢ <;>
      omega
  obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
    (2 * s + r) (s + 2 * r + 2) anchor .zero hphase hanchorMem
  exact ⟨p, Prod.ext hq hz⟩

theorem cmoDownPhase2_anchor_has_parameter
    (s r : ℕ) (anchor : Cell)
    (label : BenzelProblem6Kernel.MicroLabel)
    (hmem : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
      (downAnchorCell anchor label))
    (hphase : IsOwnerPhase (2 * s + r + 1) anchor) :
    ∃ p : SimplexPoint (2 * s + r), cmoDownPhase2Anchor p = anchor := by
  rcases anchor with ⟨q, z⟩
  let shifted : Cell := (q - 1, z)
  have hphaseLinear := hphase
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphaseLinear
  obtain ⟨phaseK, hphaseK⟩ := hphaseLinear
  have hshiftPhase : IsOwnerPhase (2 * s + r) shifted := by
    rw [IsOwnerPhase, Int.modEq_iff_dvd,
      Int.dvd_iff_emod_eq_zero] at hphase ⊢
    dsimp [shifted]
    push_cast
    omega
  have hshiftMem : inBenzel (2 * s + r + 2) (s + 2 * r + 2)
      (cellForOwnerAnchor shifted .one) := by
    cases label <;>
      dsimp [inBenzel, downAnchorCell, cellForOwnerAnchor, shifted]
        at hmem ⊢ <;> omega
  obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
    (2 * s + r) (s + 2 * r + 2) shifted .one hshiftPhase hshiftMem
  refine ⟨p, Prod.ext ?_ ?_⟩
  · dsimp [cmoDownPhase2Anchor, shifted] at hq ⊢
    omega
  · dsimp [cmoDownPhase2Anchor, shifted] at hz ⊢
    omega

theorem cmoDownParameterToAnchor_surjective
    (s r : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (cmoDownParameterToAnchor s r hs) := by
  intro anchor
  obtain ⟨label, hmem⟩ :=
    (mem_offsetDownAnchorFinset_iff
      (2 * s + r - 1) (3 * s + 1) anchor.1).1 anchor.2
  have hp := classMinusOneOffsetParameters s r hs
  rw [hp.1, hp.2] at hmem
  obtain ⟨c, hphase⟩ :=
    cmo_exists_anchor_phase_offset (2 * s + r - 1) anchor.1
  rcases c with ⟨c, hc⟩
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hcases with hcase | hcase | hcase
  · subst c
    obtain ⟨p, hanchor⟩ :=
      cmoDownPhase0_anchor_has_parameter s r hs anchor.1 label hmem hphase
    have hallowed := (cmoDownPhase0_mem_iff s r hs p).1
      ⟨label, by rwa [hanchor]⟩
    refine ⟨.phase0 ⟨p, hallowed⟩, Subtype.ext ?_⟩
    exact hanchor
  · subst c
    have ht : 2 * s + r - 1 + 1 = 2 * s + r := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase
    rw [ht] at hphase
    obtain ⟨p, hanchor⟩ :=
      cmoDownPhase1_anchor_has_parameter s r anchor.1 label hmem hphase
    have hallowed := (cmoDownPhase1_mem_iff s r hs p).1
      ⟨label, by rwa [hanchor]⟩
    refine ⟨.phase1 ⟨p, hallowed⟩, Subtype.ext ?_⟩
    exact hanchor
  · subst c
    have ht : 2 * s + r - 1 + 2 = 2 * s + r + 1 := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase
    rw [ht] at hphase
    obtain ⟨p, hanchor⟩ :=
      cmoDownPhase2_anchor_has_parameter s r anchor.1 label hmem hphase
    have hallowed := (cmoDownPhase2_mem_iff s r hs p).1
      ⟨label, by rwa [hanchor]⟩
    refine ⟨.phase2 ⟨p, hallowed⟩, Subtype.ext ?_⟩
    exact hanchor

end FiniteDefects
