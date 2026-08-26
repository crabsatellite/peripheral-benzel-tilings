import FiniteDefects.D4LiteralTiling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Exact owner-side energy of the d=4 benzel -/

namespace FiniteDefects

open scoped BigOperators

def d4OwnerLabelEnergy {m : ℕ} (p : SimplexPoint (m + 2))
    (label : MicroLabel) : ℤ :=
  ownerPotential label (ownerQ p) (ownerR p)

noncomputable def d4LiteralCellEnergy {m : ℕ} (cell : D4Cell m) : ℤ :=
  let pair := (d4OwnerCellEquiv m).symm cell
  d4OwnerLabelEnergy pair.1.1 pair.1.2

noncomputable def d4OwnerPresentEnergy {m : ℕ}
    (p : SimplexPoint (m + 2)) : ℤ := by
  classical
  exact ∑ label : MicroLabel,
    if inBenzel (m + 4) (2 * m + 4) (ownerCell p label) then
      d4OwnerLabelEnergy p label else 0

theorem microLabel_sum (f : MicroLabel → ℤ) :
    ∑ label : MicroLabel, f label = f .zero + f .one + f .two := by
  classical
  have huniv : (Finset.univ : Finset MicroLabel) =
      {.zero, .one, .two} := by
    ext label
    rcases label with _ | _ | _ <;> simp
  change (Finset.univ.sum f) = _
  rw [huniv]
  simp [add_assoc]

theorem d4_owner_label_mem_iff {m : ℕ}
    (p : SimplexPoint (m + 2)) (label : MicroLabel) :
    inBenzel (m + 4) (2 * m + 4) (ownerCell p label) ↔
      d3k1LabelPresent (k := 1) label p := by
  have hdb : 4 ≤ 2 * (m + 2) + 4 := by omega
  calc
    inBenzel (m + 4) (2 * m + 4) (ownerCell p label) ↔
        ownerLabelPresentAtOffset 4 label p := by
      simpa only [show m + 2 + 2 = m + 4 by omega,
        show 2 * (m + 2) + 4 - 4 = 2 * m + 4 by omega] using
        (ownerLabelPresentAtOffset_iff_inBenzel (m + 2) 4 hdb label p).symm
    _ ↔ d3k1LabelPresent (k := 1) label p := by
      simpa using ownerLabelPresentAtOffset_d3k1 (m + 2) 1 (by omega) label p

def cornerU (t : ℕ) : SimplexPoint t where
  u := t
  v := 0
  w := 0
  sum_eq := by omega

def cornerV (t : ℕ) : SimplexPoint t where
  u := 0
  v := t
  w := 0
  sum_eq := by omega

def cornerW (t : ℕ) : SimplexPoint t where
  u := 0
  v := 0
  w := t
  sum_eq := by omega

theorem simplex_corner_or_interior {t : ℕ} (p : SimplexPoint t) :
    p = cornerU t ∨ p = cornerV t ∨ p = cornerW t ∨
      (p.u < t ∧ p.v < t ∧ p.w < t) := by
  have hsum := p.sum_eq
  have hu : p.u ≤ t := by omega
  have hv : p.v ≤ t := by omega
  have hw : p.w ≤ t := by omega
  rcases eq_or_lt_of_le hu with hu_eq | hu_lt
  · left
    apply simplexPoint_ext <;> simp [cornerU] <;> omega
  · rcases eq_or_lt_of_le hv with hv_eq | hv_lt
    · right; left
      apply simplexPoint_ext <;> simp [cornerV] <;> omega
    · rcases eq_or_lt_of_le hw with hw_eq | hw_lt
      · right; right; left
        apply simplexPoint_ext <;> simp [cornerW] <;> omega
      · exact Or.inr (Or.inr (Or.inr ⟨hu_lt, hv_lt, hw_lt⟩))

theorem d4_cornerU_energy (m : ℕ) :
    d4OwnerPresentEnergy (cornerU (m + 2)) = (m + 2 : ℤ) := by
  classical
  simp_rw [d4OwnerPresentEnergy, d4_owner_label_mem_iff]
  rw [microLabel_sum]
  simp [d3k1LabelPresent, cornerU, d4OwnerLabelEnergy,
    ownerPotential, ownerQ, ownerR]

theorem d4_cornerV_energy (m : ℕ) :
    d4OwnerPresentEnergy (cornerV (m + 2)) = (m + 2 : ℤ) := by
  classical
  simp_rw [d4OwnerPresentEnergy, d4_owner_label_mem_iff]
  rw [microLabel_sum]
  simp [d3k1LabelPresent, cornerV, d4OwnerLabelEnergy,
    ownerPotential, ownerQ, ownerR]

theorem d4_cornerW_energy (m : ℕ) :
    d4OwnerPresentEnergy (cornerW (m + 2)) = (m + 2 : ℤ) := by
  classical
  simp_rw [d4OwnerPresentEnergy, d4_owner_label_mem_iff]
  rw [microLabel_sum]
  simp [d3k1LabelPresent, cornerW, d4OwnerLabelEnergy,
    ownerPotential, ownerQ, ownerR]

theorem d4_interior_energy_zero {m : ℕ} (p : SimplexPoint (m + 2))
    (hu : p.u < m + 2) (hv : p.v < m + 2) (hw : p.w < m + 2) :
    d4OwnerPresentEnergy p = 0 := by
  classical
  simp_rw [d4OwnerPresentEnergy, d4_owner_label_mem_iff]
  rw [microLabel_sum]
  have hsum := p.sum_eq
  have hu' : p.u ≤ m + 1 := by omega
  have hv' : p.v ≤ m + 1 := by omega
  have hw' : p.w ≤ m + 1 := by omega
  have hu2 : p.u ≤ m + 1 + 1 := by omega
  have hv2 : p.v ≤ m + 1 + 1 := by omega
  have hw2 : p.w ≤ m + 1 + 1 := by omega
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [d3k1LabelPresent]
  simp only [hsub, hu', hv', hw', hu2, hv2, hw2,
    and_self, if_true]
  simpa [d4OwnerLabelEnergy] using
    ownerPotential_sum (ownerQ p) (ownerR p)

theorem d4_owner_energy_indicator {m : ℕ}
    (p : SimplexPoint (m + 2)) :
    d4OwnerPresentEnergy p =
      if p = cornerU (m + 2) then (m + 2 : ℤ)
      else if p = cornerV (m + 2) then (m + 2 : ℤ)
      else if p = cornerW (m + 2) then (m + 2 : ℤ)
      else 0 := by
  rcases simplex_corner_or_interior p with rfl | rfl | rfl | hinterior
  · simp [d4_cornerU_energy]
  · have huv : cornerV (m + 2) ≠ cornerU (m + 2) := by
      intro h
      simpa [cornerU, cornerV] using congrArg SimplexPoint.u h
    simp [huv, d4_cornerV_energy]
  · have hwu : cornerW (m + 2) ≠ cornerU (m + 2) := by
      intro h
      simpa [cornerU, cornerW] using congrArg SimplexPoint.u h
    have hwv : cornerW (m + 2) ≠ cornerV (m + 2) := by
      intro h
      simpa [cornerV, cornerW] using congrArg SimplexPoint.v h
    simp [hwu, hwv, d4_cornerW_energy]
  · have hneU : p ≠ cornerU (m + 2) := by
      intro h
      have := congrArg SimplexPoint.u h
      simp [cornerU] at this
      omega
    have hneV : p ≠ cornerV (m + 2) := by
      intro h
      have := congrArg SimplexPoint.v h
      simp [cornerV] at this
      omega
    have hneW : p ≠ cornerW (m + 2) := by
      intro h
      have := congrArg SimplexPoint.w h
      simp [cornerW] at this
      omega
    simp [hneU, hneV, hneW,
      d4_interior_energy_zero p hinterior.1 hinterior.2.1 hinterior.2.2]

theorem d4_present_owner_label_energy_sum (m : ℕ) :
    ∑ pair : PresentD4OwnerLabel m,
        d4OwnerLabelEnergy pair.1.1 pair.1.2 =
      ∑ p : SimplexPoint (m + 2), d4OwnerPresentEnergy p := by
  classical
  calc
    (∑ pair : PresentD4OwnerLabel m,
        d4OwnerLabelEnergy pair.1.1 pair.1.2) =
        ∑ pair : D4OwnerLabelPair m,
          if IsPresentD4OwnerLabel m pair then
            d4OwnerLabelEnergy pair.1 pair.2 else 0 := by
      symm
      calc
        (∑ pair : D4OwnerLabelPair m,
            if IsPresentD4OwnerLabel m pair then
              d4OwnerLabelEnergy pair.1 pair.2 else 0) =
            ∑ pair ∈ Finset.univ.filter (IsPresentD4OwnerLabel m),
              d4OwnerLabelEnergy pair.1 pair.2 := by
          rw [Finset.sum_filter]
        _ = ∑ pair : PresentD4OwnerLabel m,
              d4OwnerLabelEnergy pair.1.1 pair.1.2 := by
          apply Finset.sum_subtype
          intro pair
          simp
    _ = ∑ p : SimplexPoint (m + 2),
          ∑ label : MicroLabel,
            if IsPresentD4OwnerLabel m (p, label) then
              d4OwnerLabelEnergy p label else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p : SimplexPoint (m + 2), d4OwnerPresentEnergy p := by
      apply Finset.sum_congr rfl
      intro p _
      unfold d4OwnerPresentEnergy IsPresentD4OwnerLabel
      apply Finset.sum_congr rfl
      intro label _
      by_cases hmem :
          inBenzel (m + 4) (2 * m + 4) (ownerCell p label) <;>
        simp [hmem]

theorem total_d4_owner_energy (m : ℕ) :
    ∑ p : SimplexPoint (m + 2), d4OwnerPresentEnergy p =
      3 * (m + 2 : ℤ) := by
  classical
  simp_rw [d4_owner_energy_indicator]
  have huv : cornerU (m + 2) ≠ cornerV (m + 2) := by
    intro h
    simpa [cornerU, cornerV] using congrArg SimplexPoint.u h
  have huw : cornerU (m + 2) ≠ cornerW (m + 2) := by
    intro h
    simpa [cornerU, cornerW] using congrArg SimplexPoint.u h
  have hvw : cornerV (m + 2) ≠ cornerW (m + 2) := by
    intro h
    simpa [cornerV, cornerW] using congrArg SimplexPoint.v h
  calc
    (∑ p : SimplexPoint (m + 2),
      if p = cornerU (m + 2) then (m + 2 : ℤ)
      else if p = cornerV (m + 2) then (m + 2 : ℤ)
      else if p = cornerW (m + 2) then (m + 2 : ℤ) else 0) =
        ∑ p : SimplexPoint (m + 2),
          ((if p = cornerU (m + 2) then (m + 2 : ℤ) else 0) +
           (if p = cornerV (m + 2) then (m + 2 : ℤ) else 0) +
           (if p = cornerW (m + 2) then (m + 2 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hu : p = cornerU (m + 2) <;>
        by_cases hv : p = cornerV (m + 2) <;>
        by_cases hw : p = cornerW (m + 2) <;>
        simp_all
    _ = 3 * (m + 2 : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp
      ring

theorem total_d4_literal_cell_energy (m : ℕ) :
    ∑ cell : D4Cell m, d4LiteralCellEnergy cell = 3 * (m + 2 : ℤ) := by
  calc
    (∑ cell : D4Cell m, d4LiteralCellEnergy cell) =
        ∑ pair : PresentD4OwnerLabel m,
          d4OwnerLabelEnergy pair.1.1 pair.1.2 := by
      apply Fintype.sum_equiv (d4OwnerCellEquiv m).symm
      intro cell
      rfl
    _ = ∑ p : SimplexPoint (m + 2), d4OwnerPresentEnergy p :=
      d4_present_owner_label_energy_sum m
    _ = 3 * (m + 2 : ℤ) := total_d4_owner_energy m

end FiniteDefects
