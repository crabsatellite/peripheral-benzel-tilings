import FiniteDefects.D4GoodComponentMv

/-! # Diagonal collapse from three variables to one -/

namespace FiniteDefects

open Finset BigOperators Finsupp

abbrev GoodFiber (degree : ℕ) := {n : GoodIndex // goodTotal n = degree}

noncomputable def goodFiberEquivSimplex (degree : ℕ) :
    GoodFiber degree ≃ SimplexPoint degree where
  toFun := fun n =>
    { u := n.1 0
      v := n.1 1
      w := n.1 2
      sum_eq := by rw [← goodTotal_coordinates, n.2] }
  invFun := fun p => ⟨goodIndex p.u p.v p.w, by
    rw [goodTotal_coordinates]
    simp only [goodIndex_zero, goodIndex_one, goodIndex_two, p.sum_eq]⟩
  left_inv := by
    intro n
    apply Subtype.ext
    exact goodIndex_coordinates n.1
  right_inv := by
    intro p
    apply simplexPoint_ext <;> simp

noncomputable def goodFiberFintype (degree : ℕ) : Fintype (GoodFiber degree) :=
  Fintype.ofEquiv (SimplexPoint degree) (goodFiberEquivSimplex degree).symm

noncomputable def goodDiagonal (f : GoodSeries) : PowerSeries ℚ :=
  PowerSeries.mk fun degree => by
    letI := goodFiberFintype degree
    exact ∑ n : GoodFiber degree, MvPowerSeries.coeff ℚ n.1 f

@[simp] theorem coeff_goodDiagonal (f : GoodSeries) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodDiagonal f) =
      letI := goodFiberFintype degree
      ∑ n : GoodFiber degree, MvPowerSeries.coeff ℚ n.1 f := by
  simp [goodDiagonal]

@[simp] theorem goodDiagonal_zero : goodDiagonal (0 : GoodSeries) = 0 := by
  ext degree
  simp [goodDiagonal]

@[simp] theorem goodDiagonal_add (f g : GoodSeries) :
    goodDiagonal (f + g) = goodDiagonal f + goodDiagonal g := by
  ext degree
  letI := goodFiberFintype degree
  simp only [coeff_goodDiagonal, map_add, Finset.sum_add_distrib]

@[simp] theorem goodDiagonal_neg (f : GoodSeries) :
    goodDiagonal (-f) = -goodDiagonal f := by
  ext degree
  letI := goodFiberFintype degree
  simp [goodDiagonal]

@[simp] theorem goodDiagonal_sub (f g : GoodSeries) :
    goodDiagonal (f - g) = goodDiagonal f - goodDiagonal g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, goodDiagonal_add, goodDiagonal_neg]

@[simp] theorem goodDiagonal_C (q : ℚ) :
    goodDiagonal (MvPowerSeries.C (Fin 3) ℚ q) = PowerSeries.C ℚ q := by
  ext degree
  rcases degree with _ | degree
  · letI := goodFiberFintype 0
    have hsingle : ∀ n : GoodFiber 0, n = ⟨0, by simp [goodTotal]⟩ := by
      intro n
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      have h := n.2
      rw [goodTotal_coordinates] at h
      fin_cases i <;> simp_all
    rw [coeff_goodDiagonal]
    rw [Fintype.sum_eq_single ⟨0, by simp [goodTotal]⟩]
    · simp
    · intro n hne
      exact (hne (hsingle n)).elim
  · letI := goodFiberFintype (degree + 1)
    rw [coeff_goodDiagonal]
    simp only [MvPowerSeries.coeff_C, PowerSeries.coeff_C]
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    intro hzero
    have htotal := n.2
    rw [hzero] at htotal
    simp [goodTotal] at htotal

@[simp] theorem goodDiagonal_one : goodDiagonal (1 : GoodSeries) = 1 := by
  rw [show (1 : GoodSeries) = MvPowerSeries.C (Fin 3) ℚ 1 by rfl,
    goodDiagonal_C]
  rfl

@[simp] theorem goodDiagonal_X (i : Fin 3) :
    goodDiagonal (MvPowerSeries.X i : GoodSeries) = PowerSeries.X := by
  ext degree
  rcases degree with _ | degree
  · letI := goodFiberFintype 0
    rw [coeff_goodDiagonal]
    rw [PowerSeries.coeff_X]
    apply Finset.sum_eq_zero
    intro n hn
    simp only [MvPowerSeries.X, MvPowerSeries.coeff_monomial]
    rw [if_neg]
    intro heq
    have htotal := n.2
    rw [heq] at htotal
    rw [goodTotal_coordinates] at htotal
    fin_cases i <;> simp at htotal
  · by_cases hdegree : degree = 0
    · subst degree
      letI := goodFiberFintype 1
      rw [coeff_goodDiagonal]
      rw [Fintype.sum_eq_single
        ⟨Finsupp.single i 1, by
          rw [goodTotal_coordinates]
          fin_cases i <;> simp⟩]
      · simp [MvPowerSeries.X]
      · intro n hne
        simp only [MvPowerSeries.X, MvPowerSeries.coeff_monomial]
        split_ifs with h
        · exact (hne (Subtype.ext h)).elim
        · rfl
    · letI := goodFiberFintype (degree + 1)
      rw [coeff_goodDiagonal]
      simp only [MvPowerSeries.X, MvPowerSeries.coeff_monomial,
        PowerSeries.coeff_X]
      rw [if_neg (by omega)]
      apply Finset.sum_eq_zero
      intro n hn
      rw [if_neg]
      intro heq
      have htotal := n.2
      rw [heq, goodTotal_coordinates] at htotal
      fin_cases i <;> simp at htotal <;> omega

end FiniteDefects
