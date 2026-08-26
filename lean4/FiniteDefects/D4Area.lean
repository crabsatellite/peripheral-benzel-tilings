import FiniteDefects.D4EnergyDoubleCount
import Mathlib.Data.Fintype.Card

/-! # Literal area and tile count on the d=4 diagonal -/

namespace FiniteDefects

abbrev MissingD4OwnerLabel (m : ℕ) :=
  {pair : D4OwnerLabelPair m // ¬IsPresentD4OwnerLabel m pair}

noncomputable instance missingD4OwnerLabelFintype (m : ℕ) :
    Fintype (MissingD4OwnerLabel m) :=
  Fintype.ofFinite (MissingD4OwnerLabel m)

inductive D4MissingSlot
  | u0 | u2 | v0 | v1 | w1 | w2
  deriving DecidableEq, Repr

instance d4MissingSlotFintype : Fintype D4MissingSlot :=
  Fintype.ofList [.u0, .u2, .v0, .v1, .w1, .w2] (by
    intro slot
    rcases slot with _ | _ | _ | _ | _ | _ <;> simp)

theorem d4_zero_missing_iff {m : ℕ} (p : SimplexPoint (m + 2)) :
    ¬IsPresentD4OwnerLabel m (p, .zero) ↔
      p = cornerU (m + 2) ∨ p = cornerV (m + 2) := by
  rw [IsPresentD4OwnerLabel, d4_owner_label_mem_iff]
  simp only [d3k1LabelPresent]
  have hsum := p.sum_eq
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  constructor
  · intro hmissing
    by_cases hu : p.u ≤ m + 1
    · right
      apply simplexPoint_ext <;> simp [cornerV] <;> omega
    · left
      apply simplexPoint_ext <;> simp [cornerU] <;> omega
  · rintro (rfl | rfl) <;> simp [cornerU, cornerV]

theorem d4_one_missing_iff {m : ℕ} (p : SimplexPoint (m + 2)) :
    ¬IsPresentD4OwnerLabel m (p, .one) ↔
      p = cornerV (m + 2) ∨ p = cornerW (m + 2) := by
  rw [IsPresentD4OwnerLabel, d4_owner_label_mem_iff]
  simp only [d3k1LabelPresent]
  have hsum := p.sum_eq
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  constructor
  · intro hmissing
    by_cases hv : p.v ≤ m + 1
    · right
      apply simplexPoint_ext <;> simp [cornerW] <;> omega
    · left
      apply simplexPoint_ext <;> simp [cornerV] <;> omega
  · rintro (rfl | rfl) <;> simp [cornerV, cornerW]

theorem d4_two_missing_iff {m : ℕ} (p : SimplexPoint (m + 2)) :
    ¬IsPresentD4OwnerLabel m (p, .two) ↔
      p = cornerU (m + 2) ∨ p = cornerW (m + 2) := by
  rw [IsPresentD4OwnerLabel, d4_owner_label_mem_iff]
  simp only [d3k1LabelPresent]
  have hsum := p.sum_eq
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  constructor
  · intro hmissing
    by_cases hu : p.u ≤ m + 1
    · right
      apply simplexPoint_ext <;> simp [cornerW] <;> omega
    · left
      apply simplexPoint_ext <;> simp [cornerU] <;> omega
  · rintro (rfl | rfl) <;> simp [cornerU, cornerW]

def d4MissingSlotPair (m : ℕ) : D4MissingSlot → D4OwnerLabelPair m
  | .u0 => (cornerU (m + 2), .zero)
  | .u2 => (cornerU (m + 2), .two)
  | .v0 => (cornerV (m + 2), .zero)
  | .v1 => (cornerV (m + 2), .one)
  | .w1 => (cornerW (m + 2), .one)
  | .w2 => (cornerW (m + 2), .two)

def d4MissingSlotToPair (m : ℕ) : D4MissingSlot → MissingD4OwnerLabel m
  | .u0 => ⟨d4MissingSlotPair m .u0, (d4_zero_missing_iff _).2 (Or.inl rfl)⟩
  | .u2 => ⟨d4MissingSlotPair m .u2, (d4_two_missing_iff _).2 (Or.inl rfl)⟩
  | .v0 => ⟨d4MissingSlotPair m .v0, (d4_zero_missing_iff _).2 (Or.inr rfl)⟩
  | .v1 => ⟨d4MissingSlotPair m .v1, (d4_one_missing_iff _).2 (Or.inl rfl)⟩
  | .w1 => ⟨d4MissingSlotPair m .w1, (d4_one_missing_iff _).2 (Or.inr rfl)⟩
  | .w2 => ⟨d4MissingSlotPair m .w2, (d4_two_missing_iff _).2 (Or.inr rfl)⟩

def missingD4PairToSlot {m : ℕ}
    (pair : MissingD4OwnerLabel m) : D4MissingSlot :=
  match pair.1.2 with
  | .zero =>
      if pair.1.1 = cornerU (m + 2) then .u0 else .v0
  | .one =>
      if pair.1.1 = cornerV (m + 2) then .v1 else .w1
  | .two =>
      if pair.1.1 = cornerU (m + 2) then .u2 else .w2

def missingD4OwnerLabelEquiv (m : ℕ) :
    MissingD4OwnerLabel m ≃ D4MissingSlot where
  toFun := missingD4PairToSlot
  invFun := d4MissingSlotToPair m
  left_inv := by
    rintro ⟨⟨p, label⟩, hmissing⟩
    rcases label with _ | _ | _
    · rcases (d4_zero_missing_iff p).1 hmissing with hp | hp
      · subst p
        apply Subtype.ext
        simp [missingD4PairToSlot, d4MissingSlotToPair, d4MissingSlotPair]
      · subst p
        have hne : cornerV (m + 2) ≠ cornerU (m + 2) := by
          intro h
          simpa [cornerU, cornerV] using congrArg SimplexPoint.u h
        apply Subtype.ext
        simp [missingD4PairToSlot, hne, d4MissingSlotToPair,
          d4MissingSlotPair]
    · rcases (d4_one_missing_iff p).1 hmissing with hp | hp
      · subst p
        apply Subtype.ext
        simp [missingD4PairToSlot, d4MissingSlotToPair, d4MissingSlotPair]
      · subst p
        have hne : cornerW (m + 2) ≠ cornerV (m + 2) := by
          intro h
          simpa [cornerV, cornerW] using congrArg SimplexPoint.v h
        apply Subtype.ext
        simp [missingD4PairToSlot, hne, d4MissingSlotToPair,
          d4MissingSlotPair]
    · rcases (d4_two_missing_iff p).1 hmissing with hp | hp
      · subst p
        apply Subtype.ext
        simp [missingD4PairToSlot, d4MissingSlotToPair, d4MissingSlotPair]
      · subst p
        have hne : cornerW (m + 2) ≠ cornerU (m + 2) := by
          intro h
          simpa [cornerU, cornerW] using congrArg SimplexPoint.u h
        apply Subtype.ext
        simp [missingD4PairToSlot, hne, d4MissingSlotToPair,
          d4MissingSlotPair]
  right_inv := by
    intro slot
    rcases slot with _ | _ | _ | _ | _ | _ <;>
      simp [missingD4PairToSlot, d4MissingSlotToPair, d4MissingSlotPair,
        cornerU, cornerV, cornerW]

theorem card_missingD4OwnerLabel (m : ℕ) :
    Fintype.card (MissingD4OwnerLabel m) = 6 := by
  rw [Fintype.card_congr (missingD4OwnerLabelEquiv m)]
  decide

theorem card_presentD4OwnerLabel (m : ℕ) :
    Fintype.card (PresentD4OwnerLabel m) =
      3 * ((m + 4).choose 2 - 2) := by
  classical
  have hpartition := Fintype.card_subtype_compl
    (fun pair : D4OwnerLabelPair m => ¬IsPresentD4OwnerLabel m pair)
  simp only [not_not] at hpartition
  have hfull : Fintype.card (D4OwnerLabelPair m) =
      (m + 4).choose 2 * 3 := by
    rw [Fintype.card_prod, card_simplexPoint]
    rw [show m + 2 + 2 = m + 4 by omega]
    have hlabels : Fintype.card MicroLabel = 3 := by decide
    rw [hlabels]
  have hchoose : 2 ≤ (m + 4).choose 2 := by
    have hmono := Nat.choose_le_choose 2 (show 3 ≤ m + 4 by omega)
    norm_num at hmono ⊢
    omega
  rw [hpartition, hfull, card_missingD4OwnerLabel m]
  omega

theorem card_d4Cell (m : ℕ) :
    Fintype.card (D4Cell m) = 3 * ((m + 4).choose 2 - 2) := by
  rw [Fintype.card_congr (d4OwnerCellEquiv m).symm,
    card_presentD4OwnerLabel]

theorem d4_tiling_card_mul_three {m : ℕ}
    (tiling : D4LiteralTiling m) :
    tiling.1.card * 3 = Fintype.card (D4Cell m) := by
  classical
  calc
    tiling.1.card * 3 =
        ∑ placement ∈ tiling.1, (d4PlacementCells placement).card := by
      simp [card_d4PlacementCells]
    _ = ∑ cell : D4Cell m,
          (tiling.1.filter fun placement =>
            D4PlacementCovers placement cell).card := by
      calc
        (∑ placement ∈ tiling.1, (d4PlacementCells placement).card) =
            ∑ placement ∈ tiling.1,
              ∑ cell : D4Cell m,
                if D4PlacementCovers placement cell then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro placement _
          have hfilter :
              Finset.univ.filter (fun cell : D4Cell m =>
                D4PlacementCovers placement cell) =
                d4PlacementCells placement := by
            ext cell
            simp [mem_d4PlacementCells_iff]
          rw [← hfilter, Finset.card_filter]
        _ = ∑ cell : D4Cell m,
              ∑ placement ∈ tiling.1,
                if D4PlacementCovers placement cell then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro cell _
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = Fintype.card (D4Cell m) := by
      have hcard (cell : D4Cell m) :
          (tiling.1.filter fun placement =>
            D4PlacementCovers placement cell).card = 1 := by
        obtain ⟨placement, hplacement⟩ :=
          d4_exact_cover_filter_singleton tiling cell
        rw [hplacement]
        simp
      simp_rw [hcard]
      simp

theorem d4_literal_tiling_card {m : ℕ} (tiling : D4LiteralTiling m) :
    tiling.1.card = (m + 4).choose 2 - 2 := by
  have hincidence := d4_tiling_card_mul_three tiling
  rw [card_d4Cell] at hincidence
  omega

end FiniteDefects
