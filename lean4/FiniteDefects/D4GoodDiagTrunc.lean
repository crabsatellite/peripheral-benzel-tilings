import FiniteDefects.D4GoodDiagPolynomial
import FiniteDefects.D4GoodDiagonal

/-! # Bounded polynomial realization of the diagonal -/

namespace FiniteDefects

open Finset BigOperators Finsupp

noncomputable def goodBound (degree : ℕ) : GoodIndex :=
  goodIndex (degree + 1) (degree + 1) (degree + 1)

theorem goodIndex_lt_goodBound_of_total_le {n : GoodIndex} {degree : ℕ}
    (h : goodTotal n ≤ degree) : n < goodBound degree := by
  rw [lt_iff_le_not_le]
  constructor
  · intro i
    fin_cases i <;> simp [goodBound, goodIndex_zero, goodIndex_one,
      goodIndex_two] <;> rw [goodTotal_coordinates] at h <;> omega
  · intro hreverse
    have h0 := hreverse 0
    rw [goodBound, goodIndex_zero] at h0
    rw [goodTotal_coordinates] at h
    omega

theorem coeff_goodDiagEval_trunc_raw (f : GoodSeries) (degree : ℕ) :
    PowerSeries.coeff ℚ degree
        (goodDiagEval (MvPowerSeries.trunc ℚ (goodBound degree) f)) =
      ∑ n ∈ Finset.Iio (goodBound degree),
        if goodTotal n = degree then MvPowerSeries.coeff ℚ n f else 0 := by
  change PowerSeries.coeff ℚ degree
      (goodDiagEval (∑ n ∈ Finset.Iio (goodBound degree),
        MvPolynomial.monomial n (MvPowerSeries.coeff ℚ n f))) = _
  rw [map_sum, map_sum]
  simp only [goodDiagEval_monomial, PowerSeries.coeff_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases htotal : goodTotal n = degree
  · rw [if_pos htotal, if_pos htotal.symm]
  · rw [if_neg htotal, if_neg (fun h => htotal h.symm)]

theorem coeff_goodDiagonal_eq_eval_trunc (f : GoodSeries) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodDiagonal f) =
      PowerSeries.coeff ℚ degree
        (goodDiagEval (MvPowerSeries.trunc ℚ (goodBound degree) f)) := by
  rw [coeff_goodDiagEval_trunc_raw]
  letI := goodFiberFintype degree
  rw [coeff_goodDiagonal]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subtype
      ((Finset.Iio (goodBound degree)).filter
        (fun n => goodTotal n = degree))
  intro n
  simp only [Finset.mem_filter, Finset.mem_Iio]
  constructor
  · exact fun h => h.2
  · intro htotal
    exact ⟨goodIndex_lt_goodBound_of_total_le htotal.le, htotal⟩

theorem coeff_goodDiagEval_eq_bound (p : MvPolynomial (Fin 3) ℚ)
    (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodDiagEval p) =
      ∑ n ∈ Finset.Iio (goodBound degree),
        if goodTotal n = degree then p.coeff n else 0 := by
  rw [coeff_goodDiagEval]
  rw [← Finset.sum_filter]
  let small := p.support.filter (fun n => goodTotal n = degree)
  let large := (Finset.Iio (goodBound degree)).filter
    (fun n => goodTotal n = degree)
  have hsubset : small ⊆ large := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.mem_Iio.mpr
      (goodIndex_lt_goodBound_of_total_le hn.2.le), hn.2⟩
  apply Finset.sum_subset hsubset
  intro n hnlarge hnsmall
  have hnSupport : n ∉ p.support := by
    intro hsupp
    apply hnsmall
    rw [Finset.mem_filter]
    exact ⟨hsupp, (Finset.mem_filter.mp hnlarge).2⟩
  simpa using hnSupport

theorem coeff_trunc_mul_eq_of_total (f g : GoodSeries)
    (index : GoodIndex) (degree : ℕ) (htotal : goodTotal index = degree) :
    (MvPowerSeries.trunc ℚ (goodBound degree) (f * g)).coeff index =
      ((MvPowerSeries.trunc ℚ (goodBound degree) f) *
        (MvPowerSeries.trunc ℚ (goodBound degree) g)).coeff index := by
  have hindex : index < goodBound degree :=
    goodIndex_lt_goodBound_of_total_le htotal.le
  rw [MvPowerSeries.coeff_trunc, if_pos hindex]
  rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hsum := Finset.mem_antidiagonal.mp hpair
  have htotalSum := congrArg goodTotal hsum
  rw [goodTotal_add, htotal] at htotalSum
  have hleft : pair.1 < goodBound degree :=
    goodIndex_lt_goodBound_of_total_le (by omega)
  have hright : pair.2 < goodBound degree :=
    goodIndex_lt_goodBound_of_total_le (by omega)
  rw [MvPowerSeries.coeff_trunc, if_pos hleft,
    MvPowerSeries.coeff_trunc, if_pos hright]

theorem coeff_goodDiagEval_trunc_mul (f g : GoodSeries) (degree : ℕ) :
    PowerSeries.coeff ℚ degree
        (goodDiagEval (MvPowerSeries.trunc ℚ (goodBound degree) (f * g))) =
      PowerSeries.coeff ℚ degree
        (goodDiagEval
          ((MvPowerSeries.trunc ℚ (goodBound degree) f) *
            (MvPowerSeries.trunc ℚ (goodBound degree) g))) := by
  rw [coeff_goodDiagEval_eq_bound, coeff_goodDiagEval_eq_bound]
  apply Finset.sum_congr rfl
  intro index hindex
  by_cases htotal : goodTotal index = degree
  · rw [if_pos htotal, if_pos htotal]
    exact coeff_trunc_mul_eq_of_total f g index degree htotal
  · rw [if_neg htotal, if_neg htotal]

theorem coeff_goodDiagEval_trunc_bound_of_le (f : GoodSeries)
    {small large : ℕ} (h : small ≤ large) :
    PowerSeries.coeff ℚ small
        (goodDiagEval (MvPowerSeries.trunc ℚ (goodBound large) f)) =
      PowerSeries.coeff ℚ small (goodDiagonal f) := by
  rw [coeff_goodDiagEval_eq_bound]
  rw [coeff_goodDiagonal_eq_eval_trunc, coeff_goodDiagEval_trunc_raw]
  apply Finset.sum_congr rfl
  intro index hindex
  by_cases htotal : goodTotal index = small
  · rw [if_pos htotal, if_pos htotal]
    rw [MvPowerSeries.coeff_trunc, if_pos]
    exact goodIndex_lt_goodBound_of_total_le (htotal.le.trans h)
  · rw [if_neg htotal, if_neg htotal]

@[simp] theorem goodDiagonal_mul (f g : GoodSeries) :
    goodDiagonal (f * g) = goodDiagonal f * goodDiagonal g := by
  ext degree
  rw [coeff_goodDiagonal_eq_eval_trunc]
  rw [coeff_goodDiagEval_trunc_mul]
  rw [map_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hsum := Finset.mem_antidiagonal.mp hpair
  rw [coeff_goodDiagEval_trunc_bound_of_le f (by omega),
    coeff_goodDiagEval_trunc_bound_of_le g (by omega)]

noncomputable def goodDiagonalRingHom : GoodSeries →+* PowerSeries ℚ where
  toFun := goodDiagonal
  map_zero' := goodDiagonal_zero
  map_one' := goodDiagonal_one
  map_add' := goodDiagonal_add
  map_mul' := goodDiagonal_mul

end FiniteDefects
