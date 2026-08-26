import FiniteDefects.OwnerBoundaryLiteral

/-! # Exact public interface for the owner-domain hierarchy -/

namespace FiniteDefects

universe u

abbrev ClassicalChoiceType := {α : Sort u} → Nonempty α → α

structure OwnerDomainHierarchyEvidence : Prop where
  cell_has_owner :
    ∀ (t b : ℕ) (cell : Cell), inBenzel (t + 2) b cell →
      ∃ (p : SimplexPoint t) (label : MicroLabel), ownerCell p label = cell
  representation_unique :
    ∀ {t : ℕ} (cell : Cell) (p p' : SimplexPoint t)
      (label label' : MicroLabel),
      ownerCell p label = cell → ownerCell p' label' = cell →
      p = p' ∧ label = label'
  d3k_owner_domain :
    ∀ (t k : ℕ), 2 * k ≤ t + 1 → ∀ p : SimplexPoint t,
      ((∃ label,
        inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p label)) ↔
        inTruncatedOwnerDomain k p)
  d3k1_owner_domain :
    ∀ (t k : ℕ), 2 * k ≤ t + 1 → ∀ p : SimplexPoint t,
      ((∃ label,
        inBenzel (t + 2) (2 * t + 4 - (3 * k + 1))
          (ownerCell p label)) ↔ inTruncatedOwnerDomain k p)
  d3k2_owner_domain :
    ∀ (t k : ℕ), 2 * k ≤ t → ∀ p : SimplexPoint t,
      ((∃ label,
        inBenzel (t + 2) (2 * t + 4 - (3 * k + 2))
          (ownerCell p label)) ↔
        p.u ≤ t - k ∧ p.v ≤ t - k ∧ p.w ≤ t - k)
  d3k2_all_labels :
    ∀ (t k : ℕ), 2 * k ≤ t → ∀ p : SimplexPoint t,
      ((∀ label,
        inBenzel (t + 2) (2 * t + 4 - (3 * k + 2))
          (ownerCell p label)) ↔
        p.u ≤ t - k ∧ p.v ≤ t - k ∧ p.w ≤ t - k)
  removed_corner_card :
    ∀ (t k : ℕ), 1 ≤ k → 2 * k ≤ t + 1 →
      Fintype.card (OutsideTruncatedOwnerDomain t k) = 3 * k.choose 2
  boundaryU_card :
    ∀ (t k : ℕ), 2 * k ≤ t + 1 → Fintype.card (BoundaryU t k) = k
  boundaryV_card :
    ∀ (t k : ℕ), 2 * k ≤ t + 1 → Fintype.card (BoundaryV t k) = k
  boundaryW_card :
    ∀ (t k : ℕ), 2 * k ≤ t + 1 → Fintype.card (BoundaryW t k) = k
  d3k_boundaryU_labels :
    ∀ (t k : ℕ) (_h : 2 * k ≤ t + 1) (p : BoundaryU t k),
      inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .zero) ∧
      inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .one) ∧
      ¬inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .two)
  d3k_boundaryV_labels :
    ∀ (t k : ℕ) (_h : 2 * k ≤ t + 1) (p : BoundaryV t k),
      ¬inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .zero) ∧
      inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .one) ∧
      inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .two)
  d3k_boundaryW_labels :
    ∀ (t k : ℕ) (_h : 2 * k ≤ t + 1) (p : BoundaryW t k),
      inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .zero) ∧
      ¬inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .one) ∧
      inBenzel (t + 2) (2 * t + 4 - 3 * k) (ownerCell p.1 .two)
  d3k1_boundaryU_labels :
    ∀ (t k : ℕ) (_h : 2 * k ≤ t + 1) (p : BoundaryU t k),
      ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .zero) ∧
      inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .one) ∧
      ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .two)
  d3k1_boundaryV_labels :
    ∀ (t k : ℕ) (_h : 2 * k ≤ t + 1) (p : BoundaryV t k),
      ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .zero) ∧
      ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .one) ∧
      inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .two)
  d3k1_boundaryW_labels :
    ∀ (t k : ℕ) (_h : 2 * k ≤ t + 1) (p : BoundaryW t k),
      inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .zero) ∧
      ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .one) ∧
      ¬inBenzel (t + 2) (2 * t + 4 - (3 * k + 1)) (ownerCell p.1 .two)

end FiniteDefects
