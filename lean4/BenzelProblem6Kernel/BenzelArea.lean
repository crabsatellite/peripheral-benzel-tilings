import BenzelProblem6Kernel.SimplexCardinality
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Literal benzel carrier and area
-/

namespace BenzelProblem6Kernel

instance microLabelFintype : Fintype MicroLabel :=
  Fintype.ofList [.zero, .one, .two] (by
    intro label
    rcases label with _ | _ | _ <;> simp)

instance peripheralBenzelDecidable (n : ℕ) (cell : Cell) :
    Decidable (inPeripheralBenzel n cell) := by
  unfold inPeripheralBenzel
  infer_instance

abbrev BenzelCell (n : ℕ) := {cell : Cell // inPeripheralBenzel n cell}

abbrev OwnerLabelPair (n : ℕ) :=
  SimplexPoint (n - 2) × MicroLabel

def IsPresentOwnerLabel (n : ℕ) (pair : OwnerLabelPair n) : Prop :=
  inPeripheralBenzel n (ownerCell pair.1 pair.2)

instance presentOwnerLabelDecidable (n : ℕ) (pair : OwnerLabelPair n) :
    Decidable (IsPresentOwnerLabel n pair) := by
  unfold IsPresentOwnerLabel
  infer_instance

abbrev PresentOwnerLabel (n : ℕ) :=
  {pair : OwnerLabelPair n // IsPresentOwnerLabel n pair}

abbrev MissingOwnerLabel (n : ℕ) :=
  {pair : OwnerLabelPair n // ¬IsPresentOwnerLabel n pair}

theorem owner_zero_missing_iff {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    ¬inPeripheralBenzel n (ownerCell p .zero) ↔
      p = sourceZero (n - 2) := by
  rw [owner_zero_mem_iff hn]
  constructor
  · intro hv
    have hsum := p.sum_eq
    apply simplexPoint_ext
    · simp [sourceZero]
      omega
    · simp [sourceZero]
      omega
    · simp [sourceZero]
      omega
  · rintro rfl
    simp [sourceZero]

theorem owner_one_missing_iff {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    ¬inPeripheralBenzel n (ownerCell p .one) ↔
      p = sourceOne (n - 2) := by
  rw [owner_one_mem_iff hn]
  constructor
  · intro hw
    have hsum := p.sum_eq
    apply simplexPoint_ext
    · simp [sourceOne]
      omega
    · simp [sourceOne]
      omega
    · simp [sourceOne]
      omega
  · rintro rfl
    simp [sourceOne]

theorem owner_two_missing_iff {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    ¬inPeripheralBenzel n (ownerCell p .two) ↔
      p = sourceTwo (n - 2) := by
  rw [owner_two_mem_iff hn]
  constructor
  · intro hu
    have hsum := p.sum_eq
    apply simplexPoint_ext
    · simp [sourceTwo]
      omega
    · simp [sourceTwo]
      omega
    · simp [sourceTwo]
      omega
  · rintro rfl
    simp [sourceTwo]

def missingOwnerLabelEquiv {n : ℕ} (hn : 5 ≤ n) :
    MissingOwnerLabel n ≃ MicroLabel where
  toFun pair := pair.1.2
  invFun label :=
    match label with
    | .zero =>
        ⟨(sourceZero (n - 2), .zero), by
          simpa [IsPresentOwnerLabel] using
            (owner_zero_missing_iff hn (sourceZero (n - 2))).2 rfl⟩
    | .one =>
        ⟨(sourceOne (n - 2), .one), by
          simpa [IsPresentOwnerLabel] using
            (owner_one_missing_iff hn (sourceOne (n - 2))).2 rfl⟩
    | .two =>
        ⟨(sourceTwo (n - 2), .two), by
          simpa [IsPresentOwnerLabel] using
            (owner_two_missing_iff hn (sourceTwo (n - 2))).2 rfl⟩
  left_inv := by
    rintro ⟨⟨p, label⟩, hmissing⟩
    rcases label with _ | _ | _
    · have hp := (owner_zero_missing_iff hn p).1 hmissing
      subst p
      rfl
    · have hp := (owner_one_missing_iff hn p).1 hmissing
      subst p
      rfl
    · have hp := (owner_two_missing_iff hn p).1 hmissing
      subst p
      rfl
  right_inv := by
    intro label
    rcases label with _ | _ | _ <;> rfl

theorem card_missingOwnerLabel {n : ℕ} (hn : 5 ≤ n) :
    Fintype.card (MissingOwnerLabel n) = 3 := by
  rw [Fintype.card_congr (missingOwnerLabelEquiv hn)]
  decide

noncomputable def chosenOwner {n : ℕ} (hn : 5 ≤ n)
    (cell : BenzelCell n) : SimplexPoint (n - 2) :=
  (benzel_cell_has_owner hn cell.1 cell.2).choose

noncomputable def chosenLabel {n : ℕ} (hn : 5 ≤ n)
    (cell : BenzelCell n) : MicroLabel :=
  (benzel_cell_has_owner hn cell.1 cell.2).choose_spec.choose

theorem chosenOwnerLabel_spec {n : ℕ} (hn : 5 ≤ n)
    (cell : BenzelCell n) :
    ownerCell (chosenOwner hn cell) (chosenLabel hn cell) = cell.1 :=
  (benzel_cell_has_owner hn cell.1 cell.2).choose_spec.choose_spec

noncomputable def chosenOwnerPair {n : ℕ} (hn : 5 ≤ n)
    (cell : BenzelCell n) : PresentOwnerLabel n :=
  ⟨(chosenOwner hn cell, chosenLabel hn cell), by
    simpa [IsPresentOwnerLabel, chosenOwnerLabel_spec hn cell] using cell.2⟩

theorem chosenOwnerPair_spec {n : ℕ} (hn : 5 ≤ n)
    (cell : BenzelCell n) :
    ownerCell (chosenOwnerPair hn cell).1.1
      (chosenOwnerPair hn cell).1.2 = cell.1 := by
  exact chosenOwnerLabel_spec hn cell

noncomputable def benzelOwnerEquiv {n : ℕ} (hn : 5 ≤ n) :
    BenzelCell n ≃ PresentOwnerLabel n where
  toFun := chosenOwnerPair hn
  invFun pair :=
    ⟨ownerCell pair.1.1 pair.1.2, pair.2⟩
  left_inv := by
    intro cell
    apply Subtype.ext
    exact chosenOwnerPair_spec hn cell
  right_inv := by
    rintro ⟨⟨p, label⟩, hpresent⟩
    have hspec := chosenOwnerPair_spec hn
      (⟨ownerCell p label, hpresent⟩ : BenzelCell n)
    obtain ⟨hp, hlabel⟩ := owner_representation_unique
      (ownerCell p label)
      (chosenOwnerPair hn ⟨ownerCell p label, hpresent⟩).1.1 p
      (chosenOwnerPair hn ⟨ownerCell p label, hpresent⟩).1.2 label
      hspec rfl
    apply Subtype.ext
    exact Prod.ext hp hlabel

noncomputable def benzelCellFintypeOf {n : ℕ} (hn : 5 ≤ n) :
    Fintype (BenzelCell n) :=
  Fintype.ofEquiv (PresentOwnerLabel n) (benzelOwnerEquiv hn).symm

theorem card_benzelCell {n : ℕ} (hn : 5 ≤ n) :
    @Fintype.card (BenzelCell n) (benzelCellFintypeOf hn) =
      3 * (n - 2) * (n + 1) / 2 := by
  classical
  letI : Fintype (BenzelCell n) := benzelCellFintypeOf hn
  rw [Fintype.card_congr (benzelOwnerEquiv hn)]
  have hpartition := Fintype.card_subtype_compl
    (fun pair : OwnerLabelPair n => ¬IsPresentOwnerLabel n pair)
  simp only [not_not] at hpartition
  have hfull : Fintype.card (OwnerLabelPair n) =
      (n : ℕ).choose 2 * 3 := by
    have hlabelcard : Fintype.card MicroLabel = 3 := by decide
    rw [Fintype.card_prod, card_simplexPoint]
    have hn2 : n - 2 + 2 = n := by omega
    rw [hn2, hlabelcard]
  rw [hpartition, hfull, card_missingOwnerLabel hn]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub1 : 5 + k - 1 = k + 4 := by omega
  have hsub2 : 5 + k - 2 = k + 3 := by omega
  have hplus1 : 5 + k + 1 = k + 6 := by omega
  have hchoose : (5 + k).choose 2 * 2 = (5 + k) * (k + 4) := by
    simpa [hsub1] using Nat.choose_succ_right_eq (5 + k) 1
  have hge : 3 ≤ (5 + k).choose 2 * 3 := by
    nlinarith
  have htwice :
      2 * ((5 + k).choose 2 * 3 - 3) =
        3 * (5 + k - 2) * (5 + k + 1) := by
    rw [hsub2, hplus1]
    have hsum :
        2 * ((5 + k).choose 2 * 3) =
          3 * (k + 3) * (k + 6) + 6 := by
      nlinarith
    omega
  calc
    (5 + k).choose 2 * 3 - 3 =
        (2 * ((5 + k).choose 2 * 3 - 3)) / 2 := by
      simp
    _ = 3 * (5 + k - 2) * (5 + k + 1) / 2 := by rw [htwice]

end BenzelProblem6Kernel
