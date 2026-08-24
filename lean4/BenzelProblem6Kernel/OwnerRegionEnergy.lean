import BenzelProblem6Kernel.OwnerPartition
import BenzelProblem6Kernel.RegionEnergy
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pointwise owner contributions to the literal benzel energy
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

def ownerLabelEnergy {t : ℕ} (p : SimplexPoint t)
    (label : MicroLabel) : ℤ :=
  ownerPotential label (ownerQ p) (ownerR p)

noncomputable def ownerPresentEnergy {n : ℕ}
    (p : SimplexPoint (n - 2)) : ℤ := by
  classical
  exact
    (if inPeripheralBenzel n (ownerCell p .zero) then
        ownerLabelEnergy p .zero else 0) +
    (if inPeripheralBenzel n (ownerCell p .one) then
        ownerLabelEnergy p .one else 0) +
    (if inPeripheralBenzel n (ownerCell p .two) then
        ownerLabelEnergy p .two else 0)

theorem simplex_corner_or_full {t : ℕ} (_ht : 0 < t)
    (p : SimplexPoint t) :
    p = sourceZero t ∨ p = sourceOne t ∨ p = sourceTwo t ∨
      (p.u < t ∧ p.v < t ∧ p.w < t) := by
  have hsum := p.sum_eq
  have hu : p.u ≤ t := by omega
  have hv : p.v ≤ t := by omega
  have hw : p.w ≤ t := by omega
  rcases eq_or_lt_of_le hu with hu_eq | hu_lt
  · right; right; left
    cases p
    simp_all [sourceTwo]
    omega
  · rcases eq_or_lt_of_le hv with hv_eq | hv_lt
    · left
      cases p
      simp_all [sourceZero]
      omega
    · rcases eq_or_lt_of_le hw with hw_eq | hw_lt
      · right; left
        cases p
        simp_all [sourceOne]
        omega
      · exact Or.inr (Or.inr (Or.inr ⟨hu_lt, hv_lt, hw_lt⟩))

theorem full_owner_present_energy_zero {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2))
    (hu : p.u < n - 2) (hv : p.v < n - 2) (hw : p.w < n - 2) :
    ownerPresentEnergy p = 0 := by
  classical
  have hzero := (owner_zero_mem_iff hn p).2 hv
  have hone := (owner_one_mem_iff hn p).2 hw
  have htwo := (owner_two_mem_iff hn p).2 hu
  simp [ownerPresentEnergy, hzero, hone, htwo, ownerLabelEnergy,
    ownerPotential_sum]

theorem sourceZero_present_energy {n : ℕ} (hn : 5 ≤ n) :
    ownerPresentEnergy (sourceZero (n - 2)) = ((n - 2 : ℕ) : ℤ) := by
  classical
  have ht : 0 < n - 2 := by omega
  have hzero :
      ¬inPeripheralBenzel n (ownerCell (sourceZero (n - 2)) .zero) := by
    rw [owner_zero_mem_iff hn]
    simp [sourceZero]
  have hone :
      inPeripheralBenzel n (ownerCell (sourceZero (n - 2)) .one) := by
    rw [owner_one_mem_iff hn]
    simp [sourceZero, ht]
  have htwo :
      inPeripheralBenzel n (ownerCell (sourceZero (n - 2)) .two) := by
    rw [owner_two_mem_iff hn]
    simp [sourceZero, ht]
  rw [ownerPresentEnergy]
  simp only [hzero, hone, htwo, if_false, if_true, zero_add]
  simpa [ownerLabelEnergy, otherLabelEnergy] using
    cornerZero_present_energy (n - 2)

theorem sourceOne_present_energy {n : ℕ} (hn : 5 ≤ n) :
    ownerPresentEnergy (sourceOne (n - 2)) = ((n - 2 : ℕ) : ℤ) := by
  classical
  have ht : 0 < n - 2 := by omega
  have hzero :
      inPeripheralBenzel n (ownerCell (sourceOne (n - 2)) .zero) := by
    rw [owner_zero_mem_iff hn]
    simp [sourceOne, ht]
  have hone :
      ¬inPeripheralBenzel n (ownerCell (sourceOne (n - 2)) .one) := by
    rw [owner_one_mem_iff hn]
    simp [sourceOne]
  have htwo :
      inPeripheralBenzel n (ownerCell (sourceOne (n - 2)) .two) := by
    rw [owner_two_mem_iff hn]
    simp [sourceOne, ht]
  rw [ownerPresentEnergy]
  simp only [hzero, hone, htwo, if_false, if_true, add_zero]
  simpa [ownerLabelEnergy, otherLabelEnergy, add_comm] using
    cornerOne_present_energy (n - 2)

theorem sourceTwo_present_energy {n : ℕ} (hn : 5 ≤ n) :
    ownerPresentEnergy (sourceTwo (n - 2)) = ((n - 2 : ℕ) : ℤ) := by
  classical
  have ht : 0 < n - 2 := by omega
  have hzero :
      inPeripheralBenzel n (ownerCell (sourceTwo (n - 2)) .zero) := by
    rw [owner_zero_mem_iff hn]
    simp [sourceTwo, ht]
  have hone :
      inPeripheralBenzel n (ownerCell (sourceTwo (n - 2)) .one) := by
    rw [owner_one_mem_iff hn]
    simp [sourceTwo, ht]
  have htwo :
      ¬inPeripheralBenzel n (ownerCell (sourceTwo (n - 2)) .two) := by
    rw [owner_two_mem_iff hn]
    simp [sourceTwo]
  rw [ownerPresentEnergy]
  simp only [hzero, hone, htwo, if_false, if_true, add_zero]
  simpa [ownerLabelEnergy, otherLabelEnergy, add_comm, add_left_comm] using
    cornerTwo_present_energy (n - 2)

theorem owner_present_energy_classification {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    (p = sourceZero (n - 2) ∨ p = sourceOne (n - 2) ∨
      p = sourceTwo (n - 2)) →
      ownerPresentEnergy p = ((n - 2 : ℕ) : ℤ) := by
  rintro (rfl | rfl | rfl)
  · exact sourceZero_present_energy hn
  · exact sourceOne_present_energy hn
  · exact sourceTwo_present_energy hn

theorem noncorner_owner_present_energy_zero {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2))
    (hcorner : p ≠ sourceZero (n - 2) ∧ p ≠ sourceOne (n - 2) ∧
      p ≠ sourceTwo (n - 2)) :
    ownerPresentEnergy p = 0 := by
  have ht : 0 < n - 2 := by omega
  rcases simplex_corner_or_full ht p with h | h | h | hfull
  · exact (hcorner.1 h).elim
  · exact (hcorner.2.1 h).elim
  · exact (hcorner.2.2 h).elim
  · exact full_owner_present_energy_zero hn p hfull.1 hfull.2.1 hfull.2.2

def simplexEmbedding (t : ℕ) :
    SimplexPoint t ↪ (Fin (t + 1) × Fin (t + 1) × Fin (t + 1)) where
  toFun p :=
    (⟨p.u, by have := p.sum_eq; omega⟩,
      ⟨p.v, by have := p.sum_eq; omega⟩,
      ⟨p.w, by have := p.sum_eq; omega⟩)
  inj' := by
    intro p q h
    have hu : p.u = q.u := congrArg (fun r => r.1.1) h
    have hvFin := congrArg (fun r => r.2.1) h
    have hwFin := congrArg (fun r => r.2.2) h
    have hv : p.v = q.v := congrArg Fin.val hvFin
    have hw : p.w = q.w := congrArg Fin.val hwFin
    cases p
    cases q
    simp_all

noncomputable instance simplexPointFintype (t : ℕ) :
    Fintype (SimplexPoint t) :=
  Fintype.ofInjective (simplexEmbedding t) (simplexEmbedding t).injective

theorem ownerPresentEnergy_eq_corner_indicator {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    ownerPresentEnergy p =
      if p = sourceZero (n - 2) then ((n - 2 : ℕ) : ℤ)
      else if p = sourceOne (n - 2) then ((n - 2 : ℕ) : ℤ)
      else if p = sourceTwo (n - 2) then ((n - 2 : ℕ) : ℤ)
      else 0 := by
  by_cases hzero : p = sourceZero (n - 2)
  · subst p
    simp [sourceZero_present_energy hn]
  · by_cases hone : p = sourceOne (n - 2)
    · subst p
      simp [hzero, sourceOne_present_energy hn]
    · by_cases htwo : p = sourceTwo (n - 2)
      · subst p
        simp [hone, hzero, sourceTwo_present_energy hn]
      · simp [hzero, hone, htwo,
          noncorner_owner_present_energy_zero hn p ⟨hzero, hone, htwo⟩]

theorem total_owner_present_energy {n : ℕ} (hn : 5 ≤ n) :
    ∑ p : SimplexPoint (n - 2), ownerPresentEnergy p =
      3 * ((n - 2 : ℕ) : ℤ) := by
  classical
  have ht : 0 < n - 2 := by omega
  have h01 : sourceZero (n - 2) ≠ sourceOne (n - 2) := by
    intro h
    have := congrArg SimplexPoint.v h
    simp [sourceZero, sourceOne] at this
    omega
  have h02 : sourceZero (n - 2) ≠ sourceTwo (n - 2) := by
    intro h
    have := congrArg SimplexPoint.u h
    simp [sourceZero, sourceTwo] at this
    omega
  have h12 : sourceOne (n - 2) ≠ sourceTwo (n - 2) := by
    intro h
    have := congrArg SimplexPoint.w h
    simp [sourceOne, sourceTwo] at this
    omega
  simp_rw [ownerPresentEnergy_eq_corner_indicator hn]
  calc
    (∑ x : SimplexPoint (n - 2),
        if x = sourceZero (n - 2) then ((n - 2 : ℕ) : ℤ)
        else if x = sourceOne (n - 2) then ((n - 2 : ℕ) : ℤ)
        else if x = sourceTwo (n - 2) then ((n - 2 : ℕ) : ℤ) else 0) =
      ∑ x : SimplexPoint (n - 2), (
        (if x = sourceZero (n - 2) then ((n - 2 : ℕ) : ℤ) else 0) +
        (if x = sourceOne (n - 2) then ((n - 2 : ℕ) : ℤ) else 0) +
        (if x = sourceTwo (n - 2) then ((n - 2 : ℕ) : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx0 : x = sourceZero (n - 2) <;>
            by_cases hx1 : x = sourceOne (n - 2) <;>
            by_cases hx2 : x = sourceTwo (n - 2) <;>
            simp_all
    _ = 3 * ((n - 2 : ℕ) : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp
      ring

end BenzelProblem6Kernel
