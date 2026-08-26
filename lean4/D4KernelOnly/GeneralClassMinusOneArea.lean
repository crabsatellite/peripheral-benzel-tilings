import D4KernelOnly.GeneralClassMinusOneOwnerArea
import D4KernelOnly.GeneralOffsetArea

/-! # Exact area and tile count for class-minus-one benzels -/

namespace FiniteDefects

noncomputable def cmoPresentOffsetOwnerLabelEquivD3K1
    (s r : ℕ) :
    PresentOffsetOwnerLabel (2 * s + r - 1) (3 * s + 1) ≃
      CMOD3K1PresentPair s r where
  toFun pair := by
    rcases pair with ⟨⟨p, label⟩, hpresent⟩
    have hdb : 3 * s + 1 ≤ 2 * (2 * s + r - 1) + 4 := by omega
    have hliteral : inBenzel ((2 * s + r - 1) + 2)
        (2 * (2 * s + r - 1) + 4 - (3 * s + 1))
        (ownerCell p label) := by
      simpa [IsPresentOffsetOwnerLabel, offsetB] using hpresent
    have hoffset : ownerLabelPresentAtOffset (3 * s + 1) label p :=
      (ownerLabelPresentAtOffset_iff_inBenzel
        (2 * s + r - 1) (3 * s + 1) hdb label p).2 hliteral
    have hd3 : d3k1LabelPresent (k := s) label p :=
      (ownerLabelPresentAtOffset_d3k1
        (2 * s + r - 1) s (by omega) label p).1 hoffset
    have hdomain : inTruncatedOwnerDomain s p :=
      (exists_ownerLabelPresentAtOffset_d3k1
        (2 * s + r - 1) s (by omega) p).1 ⟨label, hoffset⟩
    exact ⟨(⟨p, hdomain⟩, label), hd3⟩
  invFun pair := by
    rcases pair with ⟨⟨p, label⟩, hpresent⟩
    have hdb : 3 * s + 1 ≤ 2 * (2 * s + r - 1) + 4 := by omega
    have hoffset : ownerLabelPresentAtOffset (3 * s + 1) label p.1 :=
      (ownerLabelPresentAtOffset_d3k1
        (2 * s + r - 1) s (by omega) label p.1).2 hpresent
    have hliteral : inBenzel ((2 * s + r - 1) + 2)
        (2 * (2 * s + r - 1) + 4 - (3 * s + 1))
        (ownerCell p.1 label) :=
      (ownerLabelPresentAtOffset_iff_inBenzel
        (2 * s + r - 1) (3 * s + 1) hdb label p.1).1 hoffset
    exact ⟨(p.1, label), by
      unfold IsPresentOffsetOwnerLabel
      simpa [offsetB] using hliteral⟩
  left_inv := by
    intro pair
    apply Subtype.ext
    rfl
  right_inv := by
    intro pair
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

theorem card_cmoOffsetCell
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (OffsetCell (2 * s + r - 1) (3 * s + 1)) =
      3 * (Fintype.card (CMODomainPoint s r) - 2 * s) := by
  rw [← Fintype.card_congr
      (offsetOwnerCellEquiv (2 * s + r - 1) (3 * s + 1)),
    Fintype.card_congr (cmoPresentOffsetOwnerLabelEquivD3K1 s r),
    card_cmoD3K1PresentPair s r hs]

theorem card_cmoOffsetCell_choose
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (OffsetCell (2 * s + r - 1) (3 * s + 1)) =
      3 * ((2 * s + r + 1).choose 2 - 3 * s.choose 2 - 2 * s) := by
  rw [card_cmoOffsetCell s r hs,
    card_cmoTruncatedPoint_of_room (2 * s + r - 1) s hs (by omega)]
  rw [show 2 * s + r - 1 + 2 = 2 * s + r + 1 by omega]

theorem cmo_tiling_card_choose
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    tiling.1.card =
      (2 * s + r + 1).choose 2 - 3 * s.choose 2 - 2 * s := by
  have hincidence := offset_tiling_card_mul_three tiling
  rw [card_cmoOffsetCell_choose s r hs] at hincidence
  omega

theorem twice_cmo_tiling_card
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    2 * tiling.1.card = s * s + r * r + 4 * s * r + s + r := by
  rw [cmo_tiling_card_choose hs tiling]
  have hS := twice_choose_two_int s hs
  have hA := twice_choose_two_int (2 * s + r + 1) (by omega)
  push_cast at hS hA
  have hleZ : 3 * (s.choose 2 : ℤ) ≤
      ((2 * s + r + 1).choose 2 : ℤ) := by
    nlinarith
  have hle : 3 * s.choose 2 ≤ (2 * s + r + 1).choose 2 := by
    exact_mod_cast hleZ
  have htwoSZ : (2 * s : ℤ) ≤
      ((2 * s + r + 1).choose 2 : ℤ) - 3 * (s.choose 2 : ℤ) := by
    nlinarith
  have htwoS : 2 * s ≤ (2 * s + r + 1).choose 2 - 3 * s.choose 2 := by
    have hcast : ((2 * s : ℕ) : ℤ) ≤
        (((2 * s + r + 1).choose 2 - 3 * s.choose 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle]
      push_cast
      exact htwoSZ
    exact_mod_cast hcast
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub htwoS, Nat.cast_sub hle]
  push_cast
  nlinarith

end FiniteDefects
