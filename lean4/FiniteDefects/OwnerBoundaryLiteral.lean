import FiniteDefects.OwnerDomainCardinality

/-! # Literal deficient-owner boundary labels -/

namespace FiniteDefects

theorem d3k_boundaryU_literal_labels (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : BoundaryU t k) :
    inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .zero) ∧
    inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .one) ∧
    ¬inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .two) := by
  have hdb : 3 * k ≤ 2 * t + 4 := by omega
  simp_rw [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k) hdb]
  simp_rw [ownerLabelPresentAtOffset_d3k t k hroom]
  have hsum := p.1.sum_eq
  have hu := p.2
  simp [d3kLabelPresent]
  omega

theorem d3k_boundaryV_literal_labels (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : BoundaryV t k) :
    ¬inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .zero) ∧
    inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .one) ∧
    inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .two) := by
  have hdb : 3 * k ≤ 2 * t + 4 := by omega
  simp_rw [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k) hdb]
  simp_rw [ownerLabelPresentAtOffset_d3k t k hroom]
  have hsum := p.1.sum_eq
  have hv := p.2
  simp [d3kLabelPresent]
  omega

theorem d3k_boundaryW_literal_labels (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : BoundaryW t k) :
    inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .zero) ∧
    ¬inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .one) ∧
    inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .two) := by
  have hdb : 3 * k ≤ 2 * t + 4 := by omega
  simp_rw [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k) hdb]
  simp_rw [ownerLabelPresentAtOffset_d3k t k hroom]
  have hsum := p.1.sum_eq
  have hw := p.2
  simp [d3kLabelPresent]
  omega

theorem d3k1_boundaryU_literal_labels (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : BoundaryU t k) :
    ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .zero) ∧
    inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .one) ∧
    ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .two) := by
  have hdb : 3 * k + 1 ≤ 2 * t + 4 := by omega
  simp_rw [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k + 1) hdb]
  simp_rw [ownerLabelPresentAtOffset_d3k1 t k hroom]
  have hsum := p.1.sum_eq
  have hu := p.2
  simp [d3k1LabelPresent]
  omega

theorem d3k1_boundaryV_literal_labels (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : BoundaryV t k) :
    ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .zero) ∧
    ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .one) ∧
    inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .two) := by
  have hdb : 3 * k + 1 ≤ 2 * t + 4 := by omega
  simp_rw [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k + 1) hdb]
  simp_rw [ownerLabelPresentAtOffset_d3k1 t k hroom]
  have hsum := p.1.sum_eq
  have hv := p.2
  simp [d3k1LabelPresent]
  omega

theorem d3k1_boundaryW_literal_labels (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : BoundaryW t k) :
    inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .zero) ∧
    ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .one) ∧
    ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .two) := by
  have hdb : 3 * k + 1 ≤ 2 * t + 4 := by omega
  simp_rw [← ownerLabelPresentAtOffset_iff_inBenzel t (3 * k + 1) hdb]
  simp_rw [ownerLabelPresentAtOffset_d3k1 t k hroom]
  have hsum := p.1.sum_eq
  have hw := p.2
  simp [d3k1LabelPresent]
  omega

end FiniteDefects
