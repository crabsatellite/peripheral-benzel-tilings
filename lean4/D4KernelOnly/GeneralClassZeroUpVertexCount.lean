import D4KernelOnly.GeneralClassZeroUpPhase2

/-! # Exact up-type vertex count for class-zero benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czUpPhase0_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : SimplexPoint (2 * s + r - 2)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) label)) ↔
      inTruncatedOwnerDomain s p := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    cases label <;>
      simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
        ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
  · intro h
    simp only [inTruncatedOwnerDomain] at h
    by_cases h0 : inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
      ownerQ, ownerR] at h0 h1 ⊢
    omega

theorem czUpPhase1_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : SimplexPoint (2 * s + r - 1)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) label)) ↔
      inTruncatedOwnerDomain (s + 1) p := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    cases label <;>
      simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
        ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
  · intro h
    simp only [inTruncatedOwnerDomain] at h
    by_cases h0 : inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
      ownerQ, ownerR] at h0 h1 ⊢
    omega

abbrev CZUpPhase2Parameter (s r : ℕ) :=
  {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
    p.1 ∉ czUpPhase2Exceptions s r}

inductive CZUpVertexParameter (s r : ℕ)
  | phase0 : CMOTruncatedPoint (2 * s + r - 2) s → CZUpVertexParameter s r
  | phase1 : CMOTruncatedPoint (2 * s + r - 1) (s + 1) → CZUpVertexParameter s r
  | phase2 : CZUpPhase2Parameter s r → CZUpVertexParameter s r

def czUpParameterAnchor {s r : ℕ} : CZUpVertexParameter s r → Cell
  | .phase0 p => (ownerQ p.1, ownerR p.1)
  | .phase1 p => (ownerQ p.1, ownerR p.1)
  | .phase2 p => (ownerQ p.1.1, ownerR p.1.1)

theorem czUpParameterAnchor_injective
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Function.Injective (czUpParameterAnchor : CZUpVertexParameter s r → Cell) := by
  intro left right h
  cases left with
  | phase0 p => cases right with
    | phase0 q =>
      congr 1
      apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1 q.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    | phase1 q =>
      have hd := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
    | phase2 q =>
      have hd := ownerAnchor_eq_total_difference p.1 q.1.1 h
      omega
  | phase1 p => cases right with
    | phase0 q =>
      have hd := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
    | phase1 q =>
      congr 1
      apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1 q.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    | phase2 q =>
      have hd := ownerAnchor_eq_total_difference p.1 q.1.1 h
      omega
  | phase2 p => cases right with
    | phase0 q =>
      have hd := ownerAnchor_eq_total_difference p.1.1 q.1 h
      omega
    | phase1 q =>
      have hd := ownerAnchor_eq_total_difference p.1.1 q.1 h
      omega
    | phase2 q =>
      congr 1; apply Subtype.ext; apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1.1 q.1.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)

def czUpParameterToAnchor
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    CZUpVertexParameter s r →
      ↥(offsetUpAnchorFinset (2 * s + r - 2) (3 * s)) :=
  fun parameter => ⟨czUpParameterAnchor parameter, by
    rw [mem_offsetUpAnchorFinset_iff]
    have hp := classZeroOffsetParameters s r hs hr
    rw [hp.1, hp.2]
    cases parameter with
    | phase0 p => exact (czUpPhase0_mem_iff s r hs hr p.1).2 p.2
    | phase1 p => exact (czUpPhase1_mem_iff s r hs hr p.1).2 p.2
    | phase2 p => exact (czUpPhase2_mem_iff s r hs hr p.1.1).2 ⟨p.1.2, p.2⟩⟩

theorem czUpParameterToAnchor_surjective
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Function.Surjective (czUpParameterToAnchor s r hs hr) := by
  intro anchor
  obtain ⟨label, hmem⟩ := (mem_offsetUpAnchorFinset_iff
    (2 * s + r - 2) (3 * s) anchor.1).1 anchor.2
  have hp := classZeroOffsetParameters s r hs hr
  rw [hp.1, hp.2] at hmem
  have hmemFD : inBenzel (2 * s + r) (s + 2 * r)
      (cellForOwnerAnchor anchor.1 (p6LabelToFiniteDefects label)) := by
    rw [← p6_cellForOwnerAnchor_eq]; exact hmem
  obtain ⟨c, hphase⟩ := cmo_exists_anchor_phase_offset (2 * s + r - 2) anchor.1
  rcases c with ⟨c, hc⟩
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hcases with hcase | hcase | hcase
  · subst c
    have ht : 2 * s + r - 2 + 2 = 2 * s + r := by omega
    obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
      (2 * s + r - 2) (s + 2 * r) anchor.1
      (p6LabelToFiniteDefects label) hphase (by rw [ht]; exact hmemFD)
    have hb := (czUpPhase0_mem_iff s r hs hr p).1 ⟨label, by
      rw [p6_cellForOwnerAnchor_eq, hq, hz]; exact hmemFD⟩
    exact ⟨.phase0 ⟨p, hb⟩, Subtype.ext (Prod.ext hq hz)⟩
  · subst c
    have ht : 2 * s + r - 2 + 1 = 2 * s + r - 1 := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase; rw [ht] at hphase
    obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
      (2 * s + r - 1) (s + 2 * r) anchor.1
      (p6LabelToFiniteDefects label) hphase (by
        dsimp [inBenzel] at hmemFD ⊢; omega)
    have hb := (czUpPhase1_mem_iff s r hs hr p).1 ⟨label, by
      rw [p6_cellForOwnerAnchor_eq, hq, hz]; exact hmemFD⟩
    exact ⟨.phase1 ⟨p, hb⟩, Subtype.ext (Prod.ext hq hz)⟩
  · subst c
    have ht : 2 * s + r - 2 + 2 = 2 * s + r := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase; rw [ht] at hphase
    obtain ⟨p, hq, hz⟩ := phase_anchor_has_simplex
      (2 * s + r) (s + 2 * r) anchor.1
      (p6LabelToFiniteDefects label) hphase (by
        dsimp [inBenzel] at hmemFD ⊢; omega)
    have hb := (czUpPhase2_mem_iff s r hs hr p).1 ⟨label, by
      rw [p6_cellForOwnerAnchor_eq, hq, hz]; exact hmemFD⟩
    exact ⟨.phase2 ⟨⟨p, hb.1⟩, hb.2⟩, Subtype.ext (Prod.ext hq hz)⟩

end FiniteDefects
