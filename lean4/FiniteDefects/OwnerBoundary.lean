import FiniteDefects.Basic

/-! # Exact boundary-owner labels and their energy -/

namespace FiniteDefects

def d3kLabelPresent {t k : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) : Prop :=
  match label with
  | .zero => p.u ≤ t - k + 1 ∧ p.v ≤ t - k ∧ p.w ≤ t - k + 1
  | .one => p.u ≤ t - k + 1 ∧ p.v ≤ t - k + 1 ∧ p.w ≤ t - k
  | .two => p.u ≤ t - k ∧ p.v ≤ t - k + 1 ∧ p.w ≤ t - k + 1

def d3k1LabelPresent {t k : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) : Prop :=
  match label with
  | .zero => p.u ≤ t - k ∧ p.v ≤ t - k ∧ p.w ≤ t - k + 1
  | .one => p.u ≤ t - k + 1 ∧ p.v ≤ t - k ∧ p.w ≤ t - k
  | .two => p.u ≤ t - k ∧ p.v ≤ t - k + 1 ∧ p.w ≤ t - k

def boundaryU (t k j : ℕ) (hkt : k ≤ t)
    (hj : j < k) : SimplexPoint t where
  u := t - k + 1
  v := j
  w := k - 1 - j
  sum_eq := by omega

theorem d3k_boundaryU_labels (t k j : ℕ)
    (hroom : 2 * k ≤ t + 1) (hj : j < k) :
    d3kLabelPresent (k := k) .zero (boundaryU t k j (by omega) hj) ∧
    d3kLabelPresent (k := k) .one (boundaryU t k j (by omega) hj) ∧
    ¬d3kLabelPresent (k := k) .two (boundaryU t k j (by omega) hj) := by
  simp [d3kLabelPresent, boundaryU]
  omega

theorem d3k1_boundaryU_labels (t k j : ℕ)
    (hroom : 2 * k ≤ t + 1) (hj : j < k) :
    ¬d3k1LabelPresent (k := k) .zero (boundaryU t k j (by omega) hj) ∧
    d3k1LabelPresent (k := k) .one (boundaryU t k j (by omega) hj) ∧
    ¬d3k1LabelPresent (k := k) .two (boundaryU t k j (by omega) hj) := by
  simp [d3k1LabelPresent, boundaryU]
  omega

theorem d3k_boundaryU_present_energy (t k j : ℕ)
    (hkt : k ≤ t) (hj : j < k) :
    ownerPotential .zero
        (ownerQ (boundaryU t k j hkt hj))
        (ownerR (boundaryU t k j hkt hj)) +
      ownerPotential .one
        (ownerQ (boundaryU t k j hkt hj))
        (ownerR (boundaryU t k j hkt hj)) =
      (t : ℤ) - k + 1 - j := by
  simp [ownerPotential, ownerQ, ownerR, boundaryU]
  omega

theorem d3k1_boundaryU_present_energy (t k j : ℕ)
    (hkt : k ≤ t) (hj : j < k) :
    ownerPotential .one
        (ownerQ (boundaryU t k j hkt hj))
        (ownerR (boundaryU t k j hkt hj)) =
      (t : ℤ) - 2 * k + 2 + j := by
  simp [ownerPotential, ownerQ, ownerR, boundaryU]
  omega

end FiniteDefects
