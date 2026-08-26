import D4KernelOnly.GeneralClassZeroUpVertexPolynomial

/-! # Exact down-type vertex parameterization for class-zero benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

def czDownPhase0Anchor {N : ℕ} (p : SimplexPoint N) : Cell :=
  (ownerQ p + 1, ownerR p - 1)
def czDownPhase1Anchor {N : ℕ} (p : SimplexPoint N) : Cell :=
  (ownerQ p, ownerR p)
def czDownPhase2Anchor {N : ℕ} (p : SimplexPoint N) : Cell :=
  (ownerQ p + 1, ownerR p)

theorem czDownPhase0_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : SimplexPoint (2 * s + r - 1)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase0Anchor p) label)) ↔
      inTruncatedOwnerDomain s p ∧
        p.w ≠ 2 * s + r - 1 - s + 1 ∧
        p.v ≠ 2 * s + r - 1 - s + 1 := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    constructor
    · cases label <;>
        simp [inBenzel, downAnchorCell, czDownPhase0Anchor,
          ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
    constructor <;> intro heq <;> cases label <;>
      simp [inBenzel, downAnchorCell, czDownPhase0Anchor,
        ownerQ, ownerR] at h <;> omega
  · rintro ⟨hdom, hw, hv⟩
    simp only [inTruncatedOwnerDomain] at hdom
    by_cases h0 : inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase0Anchor p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase0Anchor p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    by_contra h2
    simp [inBenzel, downAnchorCell, czDownPhase0Anchor,
      ownerQ, ownerR] at h0 h1 h2
    omega

theorem czDownPhase1_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : SimplexPoint (2 * s + r - 1)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase1Anchor p) label)) ↔
      inTruncatedOwnerDomain s p ∧
        p.v ≠ 2 * s + r - 1 - s + 1 ∧
        p.u ≠ 2 * s + r - 1 - s + 1 := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    constructor
    · cases label <;>
        simp [inBenzel, downAnchorCell, czDownPhase1Anchor,
          ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
    constructor <;> intro heq <;> cases label <;>
      simp [inBenzel, downAnchorCell, czDownPhase1Anchor,
        ownerQ, ownerR] at h <;> omega
  · rintro ⟨hdom, hv, hu⟩
    simp only [inTruncatedOwnerDomain] at hdom
    by_cases h0 : inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase1Anchor p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase1Anchor p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    by_contra h2
    simp [inBenzel, downAnchorCell, czDownPhase1Anchor,
      ownerQ, ownerR] at h0 h1 h2
    omega

theorem czDownPhase2_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : SimplexPoint (2 * s + r - 1)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase2Anchor p) label)) ↔
      inTruncatedOwnerDomain s p ∧
        p.w ≠ 2 * s + r - 1 - s + 1 ∧
        p.u ≠ 2 * s + r - 1 - s + 1 := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    constructor
    · cases label <;>
        simp [inBenzel, downAnchorCell, czDownPhase2Anchor,
          ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
    constructor <;> intro heq <;> cases label <;>
      simp [inBenzel, downAnchorCell, czDownPhase2Anchor,
        ownerQ, ownerR] at h <;> omega
  · rintro ⟨hdom, hw, hu⟩
    simp only [inTruncatedOwnerDomain] at hdom
    by_cases h0 : inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase2Anchor p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r) (s + 2 * r)
        (downAnchorCell (czDownPhase2Anchor p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    by_contra h2
    simp [inBenzel, downAnchorCell, czDownPhase2Anchor,
      ownerQ, ownerR] at h0 h1 h2
    omega

abbrev CZDownPhase0Parameter (s r : ℕ) :=
  {p : CMOTruncatedPoint (2 * s + r - 1) s //
    p.1.w ≠ 2 * s + r - 1 - s + 1 ∧ p.1.v ≠ 2 * s + r - 1 - s + 1}
abbrev CZDownPhase1Parameter (s r : ℕ) :=
  {p : CMOTruncatedPoint (2 * s + r - 1) s //
    p.1.v ≠ 2 * s + r - 1 - s + 1 ∧ p.1.u ≠ 2 * s + r - 1 - s + 1}
abbrev CZDownPhase2Parameter (s r : ℕ) :=
  {p : CMOTruncatedPoint (2 * s + r - 1) s //
    p.1.w ≠ 2 * s + r - 1 - s + 1 ∧ p.1.u ≠ 2 * s + r - 1 - s + 1}

inductive CZDownVertexParameter (s r : ℕ)
  | phase0 : CZDownPhase0Parameter s r → CZDownVertexParameter s r
  | phase1 : CZDownPhase1Parameter s r → CZDownVertexParameter s r
  | phase2 : CZDownPhase2Parameter s r → CZDownVertexParameter s r

def czDownParameterAnchor {s r : ℕ} : CZDownVertexParameter s r → Cell
  | .phase0 p => czDownPhase0Anchor p.1.1
  | .phase1 p => czDownPhase1Anchor p.1.1
  | .phase2 p => czDownPhase2Anchor p.1.1

theorem czDownParameterAnchor_injective (s r : ℕ) :
    Function.Injective (czDownParameterAnchor : CZDownVertexParameter s r → Cell) := by
  intro left right h
  cases left with
  | phase0 p => cases right with
    | phase0 q =>
      congr 1; apply Subtype.ext; apply Subtype.ext; apply simplexPoint_ext <;>
        have hp := p.1.1.sum_eq <;> have hq := q.1.1.sum_eq <;>
        simp [czDownParameterAnchor, czDownPhase0Anchor, ownerQ, ownerR] at h <;> omega
    | phase1 q =>
      have hp := p.1.1.sum_eq; have hq := q.1.1.sum_eq
      simp [czDownParameterAnchor, czDownPhase0Anchor,
        czDownPhase1Anchor, ownerQ, ownerR] at h; omega
    | phase2 q =>
      have hp := p.1.1.sum_eq; have hq := q.1.1.sum_eq
      simp [czDownParameterAnchor, czDownPhase0Anchor,
        czDownPhase2Anchor, ownerQ, ownerR] at h; omega
  | phase1 p => cases right with
    | phase0 q =>
      have hp := p.1.1.sum_eq; have hq := q.1.1.sum_eq
      simp [czDownParameterAnchor, czDownPhase0Anchor,
        czDownPhase1Anchor, ownerQ, ownerR] at h; omega
    | phase1 q =>
      congr 1; apply Subtype.ext; apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1.1 q.1.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    | phase2 q =>
      have hp := p.1.1.sum_eq; have hq := q.1.1.sum_eq
      simp [czDownParameterAnchor, czDownPhase1Anchor,
        czDownPhase2Anchor, ownerQ, ownerR] at h; omega
  | phase2 p => cases right with
    | phase0 q =>
      have hp := p.1.1.sum_eq; have hq := q.1.1.sum_eq
      simp [czDownParameterAnchor, czDownPhase0Anchor,
        czDownPhase2Anchor, ownerQ, ownerR] at h; omega
    | phase1 q =>
      have hp := p.1.1.sum_eq; have hq := q.1.1.sum_eq
      simp [czDownParameterAnchor, czDownPhase1Anchor,
        czDownPhase2Anchor, ownerQ, ownerR] at h; omega
    | phase2 q =>
      congr 1; apply Subtype.ext; apply Subtype.ext; apply simplexPoint_ext <;>
        have hp := p.1.1.sum_eq <;> have hq := q.1.1.sum_eq <;>
        simp [czDownParameterAnchor, czDownPhase2Anchor, ownerQ, ownerR] at h <;> omega

def czDownParameterToAnchor
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    CZDownVertexParameter s r →
      ↥(offsetDownAnchorFinset (2 * s + r - 2) (3 * s)) :=
  fun parameter => ⟨czDownParameterAnchor parameter, by
    rw [mem_offsetDownAnchorFinset_iff]
    have hp := classZeroOffsetParameters s r hs hr
    rw [hp.1, hp.2]
    cases parameter with
    | phase0 p => exact (czDownPhase0_mem_iff s r hs hr p.1.1).2 ⟨p.1.2, p.2⟩
    | phase1 p => exact (czDownPhase1_mem_iff s r hs hr p.1.1).2 ⟨p.1.2, p.2⟩
    | phase2 p => exact (czDownPhase2_mem_iff s r hs hr p.1.1).2 ⟨p.1.2, p.2⟩⟩

end FiniteDefects
