import FiniteDefects.OwnerBoundary
import FiniteDefects.LiteralBenzel

/-! # Literal owner-cell inequalities for every peripheral residue class -/

namespace FiniteDefects

def ownerCellDifferences {t : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) : ℤ × ℤ × ℤ :=
  match label with
  | .zero => (3 * p.u - t, 3 * p.v - t + 1, 3 * p.w - t - 1)
  | .one => (3 * p.u - t - 1, 3 * p.v - t, 3 * p.w - t + 1)
  | .two => (3 * p.u - t + 1, 3 * p.v - t - 1, 3 * p.w - t)

def ownerLabelPresentAtOffset {t : ℕ} (d : ℕ) (label : MicroLabel)
    (p : SimplexPoint t) : Prop :=
  let differences := ownerCellDifferences label p
  let lower : ℤ := -(t : ℤ) - 1
  let upper : ℤ := 2 * t + 3 - d
  lower ≤ differences.1 ∧ differences.1 ≤ upper ∧
  lower ≤ differences.2.1 ∧ differences.2.1 ≤ upper ∧
  lower ≤ differences.2.2 ∧ differences.2.2 ≤ upper

theorem ownerLabelPresentAtOffset_iff_inBenzel (t d : ℕ)
    (hdb : d ≤ 2 * t + 4) (label : MicroLabel) (p : SimplexPoint t) :
    ownerLabelPresentAtOffset d label p ↔
      inBenzel (t + 2) (2 * t + 4 - d) (ownerCell p label) := by
  have hb : ((2 * t + 4 - d : ℕ) : ℤ) = 2 * (t : ℤ) + 4 - d := by
    omega
  have ha : ((t + 2 : ℕ) : ℤ) = (t : ℤ) + 2 := by omega
  rcases label with _ | _ | _
  · rcases owner_cell_zero_differences p with ⟨hzero, hone, htwo⟩
    simp only [ownerLabelPresentAtOffset, ownerCellDifferences]
    dsimp [inBenzel]
    rw [hzero, hone, htwo, hb, ha]
    omega
  · rcases owner_cell_one_differences p with ⟨hzero, hone, htwo⟩
    simp only [ownerLabelPresentAtOffset, ownerCellDifferences]
    dsimp [inBenzel]
    rw [hzero, hone, htwo, hb, ha]
    omega
  · rcases owner_cell_two_differences p with ⟨hzero, hone, htwo⟩
    simp only [ownerLabelPresentAtOffset, ownerCellDifferences]
    dsimp [inBenzel]
    rw [hzero, hone, htwo, hb, ha]
    omega

theorem ownerLabelPresentAtOffset_d3k (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (label : MicroLabel) (p : SimplexPoint t) :
    ownerLabelPresentAtOffset (3 * k) label p ↔
      d3kLabelPresent (k := k) label p := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  rcases label with _ | _ | _ <;>
    simp [ownerLabelPresentAtOffset, ownerCellDifferences,
      d3kLabelPresent] <;>
    omega

theorem ownerLabelPresentAtOffset_d3k1 (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (label : MicroLabel) (p : SimplexPoint t) :
    ownerLabelPresentAtOffset (3 * k + 1) label p ↔
      d3k1LabelPresent (k := k) label p := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  rcases label with _ | _ | _ <;>
    simp [ownerLabelPresentAtOffset, ownerCellDifferences,
      d3k1LabelPresent] <;>
    omega

theorem ownerLabelPresentAtOffset_d3k2 (t k : ℕ)
    (hroom : 2 * k ≤ t) (label : MicroLabel) (p : SimplexPoint t) :
    ownerLabelPresentAtOffset (3 * k + 2) label p ↔
      p.u ≤ t - k ∧ p.v ≤ t - k ∧ p.w ≤ t - k := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  rcases label with _ | _ | _ <;>
    simp [ownerLabelPresentAtOffset, ownerCellDifferences] <;>
    omega

def inTruncatedOwnerDomain {t : ℕ} (k : ℕ) (p : SimplexPoint t) : Prop :=
  p.u ≤ t - k + 1 ∧ p.v ≤ t - k + 1 ∧ p.w ≤ t - k + 1

theorem exists_ownerLabelPresentAtOffset_d3k (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) :
    (∃ label, ownerLabelPresentAtOffset (3 * k) label p) ↔
      inTruncatedOwnerDomain k p := by
  simp_rw [ownerLabelPresentAtOffset_d3k t k hroom]
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, hlabel⟩
    rcases label with _ | _ | _ <;>
      simp [d3kLabelPresent, inTruncatedOwnerDomain] at hlabel ⊢ <;>
      omega
  · intro hdomain
    simp only [inTruncatedOwnerDomain] at hdomain
    by_cases hu : p.u ≤ t - k
    · exact ⟨.two, by simp [d3kLabelPresent, hu, hdomain]⟩
    · by_cases hv : p.v ≤ t - k
      · exact ⟨.zero, by simp [d3kLabelPresent, hv, hdomain]⟩
      · have hw : p.w ≤ t - k := by omega
        exact ⟨.one, by simp [d3kLabelPresent, hw, hdomain]⟩

theorem exists_ownerLabelPresentAtOffset_d3k1 (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) :
    (∃ label, ownerLabelPresentAtOffset (3 * k + 1) label p) ↔
      inTruncatedOwnerDomain k p := by
  simp_rw [ownerLabelPresentAtOffset_d3k1 t k hroom]
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, hlabel⟩
    rcases label with _ | _ | _ <;>
      simp [d3k1LabelPresent, inTruncatedOwnerDomain] at hlabel ⊢ <;>
      omega
  · intro hdomain
    simp only [inTruncatedOwnerDomain] at hdomain
    by_cases hu : p.u ≤ t - k
    · by_cases hv : p.v ≤ t - k
      · exact ⟨.zero, by simp [d3k1LabelPresent, hu, hv, hdomain]⟩
      · have hw : p.w ≤ t - k := by omega
        exact ⟨.two, by simp [d3k1LabelPresent, hu, hw, hdomain]⟩
    · have hv : p.v ≤ t - k := by omega
      have hw : p.w ≤ t - k := by omega
      exact ⟨.one, by simp [d3k1LabelPresent, hv, hw, hdomain]⟩

theorem all_ownerLabelsPresentAtOffset_d3k2 (t k : ℕ)
    (hroom : 2 * k ≤ t) (p : SimplexPoint t) :
    (∀ label, ownerLabelPresentAtOffset (3 * k + 2) label p) ↔
      p.u ≤ t - k ∧ p.v ≤ t - k ∧ p.w ≤ t - k := by
  constructor
  · intro hall
    exact (ownerLabelPresentAtOffset_d3k2 t k hroom .zero p).1 (hall .zero)
  · intro hbounds label
    exact (ownerLabelPresentAtOffset_d3k2 t k hroom label p).2 hbounds

theorem owner_meets_literal_benzel_d3k (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) :
    (∃ label,
      inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p label)) ↔
      inTruncatedOwnerDomain k p := by
  have hdb : 3 * k ≤ 2 * t + 4 := by omega
  simpa only [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k) hdb] using
    exists_ownerLabelPresentAtOffset_d3k t k hroom p

theorem owner_meets_literal_benzel_d3k1 (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) :
    (∃ label,
      inBenzel (t + 2) (2 * t + 4 - (3 * k + 1))
        (ownerCell p label)) ↔
      inTruncatedOwnerDomain k p := by
  have hdb : 3 * k + 1 ≤ 2 * t + 4 := by omega
  simpa only [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k + 1) hdb] using
    exists_ownerLabelPresentAtOffset_d3k1 t k hroom p

theorem owner_labels_literal_benzel_d3k2 (t k : ℕ)
    (hroom : 2 * k ≤ t) (p : SimplexPoint t) :
    (∀ label,
      inBenzel (t + 2) (2 * t + 4 - (3 * k + 2))
        (ownerCell p label)) ↔
      p.u ≤ t - k ∧ p.v ≤ t - k ∧ p.w ≤ t - k := by
  have hdb : 3 * k + 2 ≤ 2 * t + 4 := by omega
  simpa only [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k + 2) hdb] using
    all_ownerLabelsPresentAtOffset_d3k2 t k hroom p

theorem owner_meets_literal_benzel_d3k2 (t k : ℕ)
    (hroom : 2 * k ≤ t) (p : SimplexPoint t) :
    (∃ label,
      inBenzel (t + 2) (2 * t + 4 - (3 * k + 2))
        (ownerCell p label)) ↔
      p.u ≤ t - k ∧ p.v ≤ t - k ∧ p.w ≤ t - k := by
  have hdb : 3 * k + 2 ≤ 2 * t + 4 := by omega
  constructor
  · rintro ⟨label, hlabel⟩
    have hpresent : ownerLabelPresentAtOffset (3 * k + 2) label p :=
      (ownerLabelPresentAtOffset_iff_inBenzel t (3 * k + 2) hdb label p).2
        hlabel
    exact (ownerLabelPresentAtOffset_d3k2 t k hroom label p).1 hpresent
  · intro hbounds
    refine ⟨.zero, (ownerLabelPresentAtOffset_iff_inBenzel
      t (3 * k + 2) hdb .zero p).1 ?_⟩
    exact (ownerLabelPresentAtOffset_d3k2 t k hroom .zero p).2 hbounds

end FiniteDefects
