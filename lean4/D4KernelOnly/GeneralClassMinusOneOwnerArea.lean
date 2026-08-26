import D4KernelOnly.GeneralClassMinusOneDownVertexCard
import FiniteDefects.OwnerBoundaryLiteral

/-! # Owner-label area count for class-minus-one benzels -/

namespace FiniteDefects

abbrev CMODomainPoint (s r : ℕ) :=
  CMOTruncatedPoint (2 * s + r - 1) s

abbrev CMOZeroPresentPoint (s r : ℕ) :=
  {p : CMODomainPoint s r // d3k1LabelPresent (k := s) .zero p.1}

abbrev CMOOnePresentPoint (s r : ℕ) :=
  {p : CMODomainPoint s r // d3k1LabelPresent (k := s) .one p.1}

abbrev CMOTwoPresentPoint (s r : ℕ) :=
  {p : CMODomainPoint s r // d3k1LabelPresent (k := s) .two p.1}

abbrev CMOZeroMissingPoint (s r : ℕ) :=
  {p : CMODomainPoint s r // ¬d3k1LabelPresent (k := s) .zero p.1}

noncomputable instance cmoZeroPresentPointFintype (s r : ℕ) :
    Fintype (CMOZeroPresentPoint s r) := Fintype.ofFinite _

noncomputable instance cmoOnePresentPointFintype (s r : ℕ) :
    Fintype (CMOOnePresentPoint s r) := Fintype.ofFinite _

noncomputable instance cmoTwoPresentPointFintype (s r : ℕ) :
    Fintype (CMOTwoPresentPoint s r) := Fintype.ofFinite _

noncomputable instance cmoZeroMissingPointFintype (s r : ℕ) :
    Fintype (CMOZeroMissingPoint s r) := Fintype.ofFinite _

def cmoBoundaryUInDomain
    (s r : ℕ) (hs : 1 ≤ s) (p : BoundaryU (2 * s + r - 1) s) :
    CMODomainPoint s r :=
  ⟨p.1, by
    have hsum := p.1.sum_eq
    have hu := p.2
    simp only [inTruncatedOwnerDomain]
    omega⟩

def cmoBoundaryVInDomain
    (s r : ℕ) (hs : 1 ≤ s) (p : BoundaryV (2 * s + r - 1) s) :
    CMODomainPoint s r :=
  ⟨p.1, by
    have hsum := p.1.sum_eq
    have hv := p.2
    simp only [inTruncatedOwnerDomain]
    omega⟩

def cmoZeroMissingEquivBoundarySum
    (s r : ℕ) (hs : 1 ≤ s) :
    CMOZeroMissingPoint s r ≃
      BoundaryU (2 * s + r - 1) s ⊕ BoundaryV (2 * s + r - 1) s where
  toFun p := by
    have hsum := p.1.1.sum_eq
    have hdomain := p.1.2
    have hmissing := p.2
    simp only [inTruncatedOwnerDomain] at hdomain
    simp only [d3k1LabelPresent] at hmissing
    have hcases : p.1.1.u = 2 * s + r - 1 - s + 1 ∨
        p.1.1.v = 2 * s + r - 1 - s + 1 := by
      omega
    by_cases hu : p.1.1.u = 2 * s + r - 1 - s + 1
    · exact .inl ⟨p.1.1, hu⟩
    · exact .inr ⟨p.1.1, hcases.resolve_left hu⟩
  invFun boundary := by
    rcases boundary with p | p
    · refine ⟨cmoBoundaryUInDomain s r hs p, ?_⟩
      have hsum := p.1.sum_eq
      have hu := p.2
      simp only [d3k1LabelPresent]
      change ¬(p.1.u ≤ 2 * s + r - 1 - s ∧
        p.1.v ≤ 2 * s + r - 1 - s ∧
        p.1.w ≤ 2 * s + r - 1 - s + 1)
      omega
    · refine ⟨cmoBoundaryVInDomain s r hs p, ?_⟩
      have hsum := p.1.sum_eq
      have hv := p.2
      simp only [d3k1LabelPresent]
      change ¬(p.1.u ≤ 2 * s + r - 1 - s ∧
        p.1.v ≤ 2 * s + r - 1 - s ∧
        p.1.w ≤ 2 * s + r - 1 - s + 1)
      omega
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    by_cases hu : p.1.1.u = 2 * s + r - 1 - s + 1
    · simp [hu, cmoBoundaryUInDomain]
    · simp [hu, cmoBoundaryVInDomain]
  right_inv := by
    intro boundary
    rcases boundary with p | p
    · have hsum := p.1.sum_eq
      have hu := p.2
      simp [cmoBoundaryUInDomain, hu]
    · have hsum := p.1.sum_eq
      have hv := p.2
      have hne : p.1.u ≠ 2 * s + r - 1 - s + 1 := by
        intro hu
        omega
      simp [cmoBoundaryVInDomain, hne]

theorem card_cmoZeroMissingPoint
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMOZeroMissingPoint s r) = 2 * s := by
  rw [Fintype.card_congr (cmoZeroMissingEquivBoundarySum s r hs),
    Fintype.card_sum,
    card_boundaryU (2 * s + r - 1) s (by omega),
    card_boundaryV (2 * s + r - 1) s (by omega)]
  omega

noncomputable def cmoZeroPresentMissingEquiv (s r : ℕ) :
    CMOZeroPresentPoint s r ⊕ CMOZeroMissingPoint s r ≃
      CMODomainPoint s r where
  toFun item := by
    rcases item with p | p
    · exact p.1
    · exact p.1
  invFun p := by
    by_cases hpresent : d3k1LabelPresent (k := s) .zero p.1
    · exact .inl ⟨p, hpresent⟩
    · exact .inr ⟨p, hpresent⟩
  left_inv := by
    intro item
    rcases item with p | p
    · dsimp
      split
      · rfl
      · rename_i h
        exact (h p.2).elim
    · dsimp
      split
      · rename_i h
        exact (p.2 h).elim
      · rfl
  right_inv := by
    intro p
    by_cases hpresent : d3k1LabelPresent (k := s) .zero p.1
    · simp [hpresent]
    · simp [hpresent]

theorem card_cmoZeroPresentPoint
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMOZeroPresentPoint s r) =
      Fintype.card (CMODomainPoint s r) - 2 * s := by
  have hpartition := Fintype.card_congr
    (cmoZeroPresentMissingEquiv s r)
  rw [Fintype.card_sum, card_cmoZeroMissingPoint s r hs] at hpartition
  omega

def cmoOnePresentEquivZeroPresent (s r : ℕ) :
    CMOOnePresentPoint s r ≃ CMOZeroPresentPoint s r where
  toFun p :=
    ⟨⟨rotateOwner (2 * s + r - 1) p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.1, h.2.2, h.1⟩⟩, by
      have h := p.2
      simp [d3k1LabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.1, h.2.2, h.1⟩⟩
  invFun p :=
    ⟨⟨(rotateOwner (2 * s + r - 1)).symm p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.2, h.1, h.2.1⟩⟩, by
      have h := p.2
      simp [d3k1LabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.2, h.1, h.2.1⟩⟩
  left_inv := by intro p; apply Subtype.ext; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; simp

def cmoTwoPresentEquivZeroPresent (s r : ℕ) :
    CMOTwoPresentPoint s r ≃ CMOZeroPresentPoint s r where
  toFun p :=
    ⟨⟨rotateOwner (2 * s + r - 1)
          (rotateOwner (2 * s + r - 1) p.1.1), by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.2, h.1, h.2.1⟩⟩, by
      have h := p.2
      simp [d3k1LabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.2, h.1, h.2.1⟩⟩
  invFun p :=
    ⟨⟨rotateOwner (2 * s + r - 1) p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.1, h.2.2, h.1⟩⟩, by
      have h := p.2
      simp [d3k1LabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.1, h.2.2, h.1⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    apply simplexPoint_ext <;> rfl
  right_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    apply simplexPoint_ext <;> rfl

abbrev CMOD3K1PresentPair (s r : ℕ) :=
  {pair : CMODomainPoint s r × MicroLabel //
    d3k1LabelPresent (k := s) pair.2 pair.1.1}

noncomputable instance cmoD3K1PresentPairFintype (s r : ℕ) :
    Fintype (CMOD3K1PresentPair s r) := Fintype.ofFinite _

def cmoD3K1PresentPairEquivSum (s r : ℕ) :
    CMOD3K1PresentPair s r ≃
      CMOZeroPresentPoint s r ⊕
        (CMOOnePresentPoint s r ⊕ CMOTwoPresentPoint s r) where
  toFun pair := by
    rcases pair with ⟨⟨p, label⟩, hpresent⟩
    rcases label with _ | _ | _
    · exact .inl ⟨p, hpresent⟩
    · exact .inr (.inl ⟨p, hpresent⟩)
    · exact .inr (.inr ⟨p, hpresent⟩)
  invFun item := by
    rcases item with p | p
    · exact ⟨(p.1, .zero), p.2⟩
    · rcases p with p | p
      · exact ⟨(p.1, .one), p.2⟩
      · exact ⟨(p.1, .two), p.2⟩
  left_inv := by intro pair; rcases pair with ⟨⟨p, label⟩, h⟩; cases label <;> rfl
  right_inv := by
    intro item
    rcases item with p | p
    · rfl
    · rcases p <;> rfl

theorem card_cmoD3K1PresentPair
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMOD3K1PresentPair s r) =
      3 * (Fintype.card (CMODomainPoint s r) - 2 * s) := by
  rw [Fintype.card_congr (cmoD3K1PresentPairEquivSum s r),
    Fintype.card_sum, Fintype.card_sum,
    Fintype.card_congr (cmoOnePresentEquivZeroPresent s r),
    Fintype.card_congr (cmoTwoPresentEquivZeroPresent s r),
    card_cmoZeroPresentPoint s r hs]
  omega

end FiniteDefects
