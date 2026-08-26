import D4KernelOnly.GeneralClassMinusOneVertexCount

/-! # Down-type vertex count for class-minus-one benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

def cmoDownException0 (s r : ℕ) : SimplexPoint (2 * s + r) where
  u := 0
  v := s + r
  w := s
  sum_eq := by omega

def cmoDownException1 (s r : ℕ) : SimplexPoint (2 * s + r) where
  u := s + r
  v := s
  w := 0
  sum_eq := by omega

def cmoDownException2 (s r : ℕ) : SimplexPoint (2 * s + r) where
  u := s
  v := 0
  w := s + r
  sum_eq := by omega

def cmoDownPhase0Anchor {N : ℕ} (p : SimplexPoint N) : Cell :=
  (ownerQ p + 1, ownerR p - 1)

def cmoDownPhase1Anchor {N : ℕ} (p : SimplexPoint N) : Cell :=
  (ownerQ p, ownerR p)

def cmoDownPhase2Anchor {N : ℕ} (p : SimplexPoint N) : Cell :=
  (ownerQ p + 1, ownerR p)

theorem cmoDownPhase0_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (p : SimplexPoint (2 * s + r)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase0Anchor p) label)) ↔
      inTruncatedOwnerDomain (s + 1) p ∧ p ≠ cmoDownException0 s r := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    constructor
    · cases label <;>
        simp [inBenzel, downAnchorCell, cmoDownPhase0Anchor,
          ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
    · intro hp
      subst p
      cases label <;>
        simp [inBenzel, downAnchorCell, cmoDownPhase0Anchor,
          ownerQ, ownerR, cmoDownException0] at h <;> omega
  · rintro ⟨hdom, hne⟩
    simp only [inTruncatedOwnerDomain] at hdom
    by_cases h0 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase0Anchor p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase0Anchor p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    by_contra h2
    apply hne
    apply simplexPoint_ext <;>
      simp [inBenzel, downAnchorCell, cmoDownPhase0Anchor,
        ownerQ, ownerR] at h0 h1 h2 ⊢ <;>
      simp [cmoDownException0] <;> omega

theorem cmoDownPhase1_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (p : SimplexPoint (2 * s + r)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase1Anchor p) label)) ↔
      inTruncatedOwnerDomain (s + 1) p ∧ p ≠ cmoDownException1 s r := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    constructor
    · cases label <;>
        simp [inBenzel, downAnchorCell, cmoDownPhase1Anchor,
          ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
    · intro hp
      subst p
      cases label <;>
        simp [inBenzel, downAnchorCell, cmoDownPhase1Anchor,
          ownerQ, ownerR, cmoDownException1] at h <;> omega
  · rintro ⟨hdom, hne⟩
    simp only [inTruncatedOwnerDomain] at hdom
    by_cases h0 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase1Anchor p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase1Anchor p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    by_contra h2
    apply hne
    apply simplexPoint_ext <;>
      simp [inBenzel, downAnchorCell, cmoDownPhase1Anchor,
        ownerQ, ownerR] at h0 h1 h2 ⊢ <;>
      simp [cmoDownException1] <;> omega

theorem cmoDownPhase2_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (p : SimplexPoint (2 * s + r)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase2Anchor p) label)) ↔
      inTruncatedOwnerDomain (s + 1) p ∧ p ≠ cmoDownException2 s r := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    constructor
    · cases label <;>
        simp [inBenzel, downAnchorCell, cmoDownPhase2Anchor,
          ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
    · intro hp
      subst p
      cases label <;>
        simp [inBenzel, downAnchorCell, cmoDownPhase2Anchor,
          ownerQ, ownerR, cmoDownException2] at h <;> omega
  · rintro ⟨hdom, hne⟩
    simp only [inTruncatedOwnerDomain] at hdom
    by_cases h0 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase2Anchor p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (downAnchorCell (cmoDownPhase2Anchor p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    by_contra h2
    apply hne
    apply simplexPoint_ext <;>
      simp [inBenzel, downAnchorCell, cmoDownPhase2Anchor,
        ownerQ, ownerR] at h0 h1 h2 ⊢ <;>
      simp [cmoDownException2] <;> omega

abbrev CMODownPhase0Parameter (s r : ℕ) :=
  {p : SimplexPoint (2 * s + r) //
    inTruncatedOwnerDomain (s + 1) p ∧ p ≠ cmoDownException0 s r}

abbrev CMODownPhase1Parameter (s r : ℕ) :=
  {p : SimplexPoint (2 * s + r) //
    inTruncatedOwnerDomain (s + 1) p ∧ p ≠ cmoDownException1 s r}

abbrev CMODownPhase2Parameter (s r : ℕ) :=
  {p : SimplexPoint (2 * s + r) //
    inTruncatedOwnerDomain (s + 1) p ∧ p ≠ cmoDownException2 s r}

inductive CMODownVertexParameter (s r : ℕ)
  | phase0 : CMODownPhase0Parameter s r → CMODownVertexParameter s r
  | phase1 : CMODownPhase1Parameter s r → CMODownVertexParameter s r
  | phase2 : CMODownPhase2Parameter s r → CMODownVertexParameter s r

def cmoDownParameterAnchor {s r : ℕ} :
    CMODownVertexParameter s r → Cell
  | .phase0 p => cmoDownPhase0Anchor p.1
  | .phase1 p => cmoDownPhase1Anchor p.1
  | .phase2 p => cmoDownPhase2Anchor p.1

theorem cmoDownParameterAnchor_injective (s r : ℕ) :
    Function.Injective (cmoDownParameterAnchor :
      CMODownVertexParameter s r → Cell) := by
  intro left right h
  cases left with
  | phase0 p => cases right with
    | phase0 q =>
      congr 1
      apply Subtype.ext
      apply simplexPoint_ext <;>
        have hp := p.1.sum_eq <;>
        have hq := q.1.sum_eq <;>
        simp [cmoDownParameterAnchor, cmoDownPhase0Anchor,
          ownerQ, ownerR] at h <;> omega
    | phase1 q =>
      have hp := p.1.sum_eq
      have hq := q.1.sum_eq
      simp [cmoDownParameterAnchor, cmoDownPhase0Anchor,
        cmoDownPhase1Anchor, ownerQ, ownerR] at h
      omega
    | phase2 q =>
      have hp := p.1.sum_eq
      have hq := q.1.sum_eq
      simp [cmoDownParameterAnchor, cmoDownPhase0Anchor,
        cmoDownPhase2Anchor, ownerQ, ownerR] at h
      omega
  | phase1 p => cases right with
    | phase0 q =>
      have hp := p.1.sum_eq
      have hq := q.1.sum_eq
      simp [cmoDownParameterAnchor, cmoDownPhase0Anchor,
        cmoDownPhase1Anchor, ownerQ, ownerR] at h
      omega
    | phase1 q =>
      congr 1
      apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1 q.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    | phase2 q =>
      have hp := p.1.sum_eq
      have hq := q.1.sum_eq
      simp [cmoDownParameterAnchor, cmoDownPhase1Anchor,
        cmoDownPhase2Anchor, ownerQ, ownerR] at h
      omega
  | phase2 p => cases right with
    | phase0 q =>
      have hp := p.1.sum_eq
      have hq := q.1.sum_eq
      simp [cmoDownParameterAnchor, cmoDownPhase0Anchor,
        cmoDownPhase2Anchor, ownerQ, ownerR] at h
      omega
    | phase1 q =>
      have hp := p.1.sum_eq
      have hq := q.1.sum_eq
      simp [cmoDownParameterAnchor, cmoDownPhase1Anchor,
        cmoDownPhase2Anchor, ownerQ, ownerR] at h
      omega
    | phase2 q =>
      congr 1
      apply Subtype.ext
      apply simplexPoint_ext <;>
        have hp := p.1.sum_eq <;>
        have hq := q.1.sum_eq <;>
        simp [cmoDownParameterAnchor, cmoDownPhase2Anchor,
          ownerQ, ownerR] at h <;> omega

def cmoDownParameterToAnchor
    (s r : ℕ) (hs : 1 ≤ s) :
    CMODownVertexParameter s r →
      ↥(offsetDownAnchorFinset (2 * s + r - 1) (3 * s + 1)) :=
  fun parameter => ⟨cmoDownParameterAnchor parameter, by
    rw [mem_offsetDownAnchorFinset_iff]
    have hp := classMinusOneOffsetParameters s r hs
    rw [hp.1, hp.2]
    cases parameter with
    | phase0 p => exact (cmoDownPhase0_mem_iff s r hs p.1).2 p.2
    | phase1 p => exact (cmoDownPhase1_mem_iff s r hs p.1).2 p.2
    | phase2 p => exact (cmoDownPhase2_mem_iff s r hs p.1).2 p.2⟩

end FiniteDefects
