import D4KernelOnly.GeneralClassZeroAlternation
import D4KernelOnly.GeneralClassMinusOneArea

/-! # Exact area and tile count for class-zero benzels -/

namespace FiniteDefects

abbrev CZDomainPoint (s r : ℕ) := CMOTruncatedPoint (2 * s + r - 2) s

abbrev CZZeroPresentPoint (s r : ℕ) :=
  {p : CZDomainPoint s r // d3kLabelPresent (k := s) .zero p.1}
abbrev CZOnePresentPoint (s r : ℕ) :=
  {p : CZDomainPoint s r // d3kLabelPresent (k := s) .one p.1}
abbrev CZTwoPresentPoint (s r : ℕ) :=
  {p : CZDomainPoint s r // d3kLabelPresent (k := s) .two p.1}
abbrev CZZeroMissingPoint (s r : ℕ) :=
  {p : CZDomainPoint s r // ¬d3kLabelPresent (k := s) .zero p.1}

noncomputable instance czZeroPresentPointFintype (s r : ℕ) :
    Fintype (CZZeroPresentPoint s r) := Fintype.ofFinite _
noncomputable instance czOnePresentPointFintype (s r : ℕ) :
    Fintype (CZOnePresentPoint s r) := Fintype.ofFinite _
noncomputable instance czTwoPresentPointFintype (s r : ℕ) :
    Fintype (CZTwoPresentPoint s r) := Fintype.ofFinite _
noncomputable instance czZeroMissingPointFintype (s r : ℕ) :
    Fintype (CZZeroMissingPoint s r) := Fintype.ofFinite _

def czBoundaryVInDomain
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : BoundaryV (2 * s + r - 2) s) : CZDomainPoint s r :=
  ⟨p.1, by
    have hsum := p.1.sum_eq
    have hv := p.2
    simp only [inTruncatedOwnerDomain]
    omega⟩

def czZeroMissingEquivBoundaryV
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    CZZeroMissingPoint s r ≃ BoundaryV (2 * s + r - 2) s where
  toFun p := by
    refine ⟨p.1.1, ?_⟩
    have hdomain := p.1.2
    have hmissing := p.2
    simp only [inTruncatedOwnerDomain] at hdomain
    simp only [d3kLabelPresent] at hmissing
    omega
  invFun p := by
    refine ⟨czBoundaryVInDomain s r hs hr p, ?_⟩
    have hsum := p.1.sum_eq
    have hv := p.2
    simp only [d3kLabelPresent]
    change ¬((czBoundaryVInDomain s r hs hr p).1.u ≤ 2 * s + r - 2 - s + 1 ∧
      (czBoundaryVInDomain s r hs hr p).1.v ≤ 2 * s + r - 2 - s ∧
      (czBoundaryVInDomain s r hs hr p).1.w ≤ 2 * s + r - 2 - s + 1)
    change ¬(p.1.u ≤ _ ∧ p.1.v ≤ _ ∧ p.1.w ≤ _)
    omega
  left_inv := by intro p; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro p; apply Subtype.ext; rfl

theorem card_czZeroMissingPoint
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Fintype.card (CZZeroMissingPoint s r) = s := by
  rw [Fintype.card_congr (czZeroMissingEquivBoundaryV s r hs hr),
    card_boundaryV (2 * s + r - 2) s (by omega)]

noncomputable def czZeroPresentMissingEquiv (s r : ℕ) :
    CZZeroPresentPoint s r ⊕ CZZeroMissingPoint s r ≃ CZDomainPoint s r where
  toFun item := by rcases item with p | p <;> exact p.1
  invFun p := by
    by_cases hp : d3kLabelPresent (k := s) .zero p.1
    · exact .inl ⟨p, hp⟩
    · exact .inr ⟨p, hp⟩
  left_inv := by
    intro item
    rcases item with p | p
    · dsimp; split
      · rfl
      · rename_i h; exact (h p.2).elim
    · dsimp; split
      · rename_i h; exact (p.2 h).elim
      · rfl
  right_inv := by
    intro p
    by_cases hp : d3kLabelPresent (k := s) .zero p.1 <;> simp [hp]

theorem card_czZeroPresentPoint
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Fintype.card (CZZeroPresentPoint s r) =
      Fintype.card (CZDomainPoint s r) - s := by
  have hpartition := Fintype.card_congr (czZeroPresentMissingEquiv s r)
  rw [Fintype.card_sum, card_czZeroMissingPoint s r hs hr] at hpartition
  omega

def czOnePresentEquivZeroPresent (s r : ℕ) :
    CZOnePresentPoint s r ≃ CZZeroPresentPoint s r where
  toFun p :=
    ⟨⟨rotateOwner (2 * s + r - 2) p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.1, h.2.2, h.1⟩⟩, by
      have h := p.2
      simp [d3kLabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.1, h.2.2, h.1⟩⟩
  invFun p :=
    ⟨⟨(rotateOwner (2 * s + r - 2)).symm p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.2, h.1, h.2.1⟩⟩, by
      have h := p.2
      simp [d3kLabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.2, h.1, h.2.1⟩⟩
  left_inv := by intro p; apply Subtype.ext; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; simp

def czTwoPresentEquivZeroPresent (s r : ℕ) :
    CZTwoPresentPoint s r ≃ CZZeroPresentPoint s r where
  toFun p :=
    ⟨⟨rotateOwner (2 * s + r - 2) (rotateOwner (2 * s + r - 2) p.1.1), by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.2, h.1, h.2.1⟩⟩, by
      have h := p.2
      simp [d3kLabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.2, h.1, h.2.1⟩⟩
  invFun p :=
    ⟨⟨rotateOwner (2 * s + r - 2) p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.1, h.2.2, h.1⟩⟩, by
      have h := p.2
      simp [d3kLabelPresent, rotateOwner] at h ⊢
      exact ⟨h.2.1, h.2.2, h.1⟩⟩
  left_inv := by intro p; apply Subtype.ext; apply Subtype.ext; apply simplexPoint_ext <;> rfl
  right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; apply simplexPoint_ext <;> rfl

abbrev CZD3KPresentPair (s r : ℕ) :=
  {pair : CZDomainPoint s r × MicroLabel //
    d3kLabelPresent (k := s) pair.2 pair.1.1}

noncomputable instance czD3KPresentPairFintype (s r : ℕ) :
    Fintype (CZD3KPresentPair s r) := Fintype.ofFinite _

def czD3KPresentPairEquivSum (s r : ℕ) :
    CZD3KPresentPair s r ≃
      CZZeroPresentPoint s r ⊕ (CZOnePresentPoint s r ⊕ CZTwoPresentPoint s r) where
  toFun pair := by
    rcases pair with ⟨⟨p, label⟩, hp⟩
    cases label
    · exact .inl ⟨p, hp⟩
    · exact .inr (.inl ⟨p, hp⟩)
    · exact .inr (.inr ⟨p, hp⟩)
  invFun item := by
    rcases item with p | p
    · exact ⟨(p.1, .zero), p.2⟩
    · rcases p with p | p
      · exact ⟨(p.1, .one), p.2⟩
      · exact ⟨(p.1, .two), p.2⟩
  left_inv := by intro pair; rcases pair with ⟨⟨p, label⟩, hp⟩; cases label <;> rfl
  right_inv := by intro item; rcases item with p | p; rfl; rcases p <;> rfl

theorem card_czD3KPresentPair
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Fintype.card (CZD3KPresentPair s r) =
      3 * (Fintype.card (CZDomainPoint s r) - s) := by
  rw [Fintype.card_congr (czD3KPresentPairEquivSum s r),
    Fintype.card_sum, Fintype.card_sum,
    Fintype.card_congr (czOnePresentEquivZeroPresent s r),
    Fintype.card_congr (czTwoPresentEquivZeroPresent s r),
    card_czZeroPresentPoint s r hs hr]
  omega

noncomputable def czPresentOffsetOwnerLabelEquivD3K
    (s r : ℕ) (hr : 1 ≤ r) :
    PresentOffsetOwnerLabel (2 * s + r - 2) (3 * s) ≃ CZD3KPresentPair s r where
  toFun pair := by
    rcases pair with ⟨⟨p, label⟩, hp⟩
    have hdb : 3 * s ≤ 2 * (2 * s + r - 2) + 4 := by omega
    have hlit : inBenzel ((2 * s + r - 2) + 2)
        (2 * (2 * s + r - 2) + 4 - 3 * s) (ownerCell p label) := by
      simpa [IsPresentOffsetOwnerLabel, offsetB] using hp
    have hoff := (ownerLabelPresentAtOffset_iff_inBenzel
      (2 * s + r - 2) (3 * s) hdb label p).2 hlit
    have hd3 := (ownerLabelPresentAtOffset_d3k
      (2 * s + r - 2) s (by omega) label p).1 hoff
    have hdom := (exists_ownerLabelPresentAtOffset_d3k
      (2 * s + r - 2) s (by omega) p).1 ⟨label, hoff⟩
    exact ⟨(⟨p, hdom⟩, label), hd3⟩
  invFun pair := by
    rcases pair with ⟨⟨p, label⟩, hp⟩
    have hdb : 3 * s ≤ 2 * (2 * s + r - 2) + 4 := by omega
    have hoff := (ownerLabelPresentAtOffset_d3k
      (2 * s + r - 2) s (by omega) label p.1).2 hp
    have hlit := (ownerLabelPresentAtOffset_iff_inBenzel
      (2 * s + r - 2) (3 * s) hdb label p.1).1 hoff
    exact ⟨(p.1, label), by
      unfold IsPresentOffsetOwnerLabel
      simpa [offsetB] using hlit⟩
  left_inv := by intro pair; apply Subtype.ext; rfl
  right_inv := by
    intro pair; apply Subtype.ext; apply Prod.ext
    · apply Subtype.ext; rfl
    · rfl

theorem card_czOffsetCell_choose
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Fintype.card (OffsetCell (2 * s + r - 2) (3 * s)) =
      3 * ((2 * s + r).choose 2 - 3 * s.choose 2 - s) := by
  rw [← Fintype.card_congr (offsetOwnerCellEquiv (2 * s + r - 2) (3 * s)),
    Fintype.card_congr (czPresentOffsetOwnerLabelEquivD3K s r hr),
    card_czD3KPresentPair s r hs hr,
    card_cmoTruncatedPoint_of_room (2 * s + r - 2) s hs (by omega)]
  rw [show 2 * s + r - 2 + 2 = 2 * s + r by omega]

abbrev CZLiteralTiling (s r : ℕ) := OffsetLiteralTiling (2 * s + r - 2) (3 * s)

theorem cz_tiling_card_choose
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r) (tiling : CZLiteralTiling s r) :
    tiling.1.card = (2 * s + r).choose 2 - 3 * s.choose 2 - s := by
  have hinc := offset_tiling_card_mul_three tiling
  rw [card_czOffsetCell_choose s r hs hr] at hinc
  omega

theorem twice_cz_tiling_card
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r) (tiling : CZLiteralTiling s r) :
    2 * tiling.1.card = s * s + r * r + 4 * s * r - (s + r) := by
  rw [cz_tiling_card_choose hs hr tiling]
  have hS := twice_choose_two_int s hs
  have hA := twice_choose_two_int (2 * s + r) (by omega)
  push_cast at hS hA
  have hleZ : 3 * (s.choose 2 : ℤ) ≤ ((2 * s + r).choose 2 : ℤ) := by nlinarith
  have hle : 3 * s.choose 2 ≤ (2 * s + r).choose 2 := by exact_mod_cast hleZ
  have hsZ : (s : ℤ) ≤ ((2 * s + r).choose 2 : ℤ) - 3 * (s.choose 2 : ℤ) := by
    nlinarith
  have hsle : s ≤ (2 * s + r).choose 2 - 3 * s.choose 2 := by
    have hcast : (s : ℤ) ≤ (((2 * s + r).choose 2 - 3 * s.choose 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle]; push_cast; exact hsZ
    exact_mod_cast hcast
  have htarget : s + r ≤ s * s + r * r + 4 * s * r := by nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hsle, Nat.cast_sub hle, Nat.cast_sub htarget]
  push_cast
  nlinarith

end FiniteDefects
