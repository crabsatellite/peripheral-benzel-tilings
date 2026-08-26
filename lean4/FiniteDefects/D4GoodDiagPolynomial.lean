import FiniteDefects.D4GoodExpansion
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-! # Polynomial diagonal evaluation used for bounded series coefficients -/

namespace FiniteDefects

open Finset BigOperators Finsupp

noncomputable def goodDiagEval :
    MvPolynomial (Fin 3) ℚ →+* PowerSeries ℚ :=
  MvPolynomial.eval₂Hom (PowerSeries.C ℚ) (fun _ => PowerSeries.X)

theorem goodTotal_eq_finsupp_sum (n : GoodIndex) :
    goodTotal n = n.sum fun _ degree => degree := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [goodTotal, Fin.sum_univ_succ]
  omega

theorem goodDiagEval_monomial (n : GoodIndex) (q : ℚ) :
    goodDiagEval (MvPolynomial.monomial n q) =
      PowerSeries.C ℚ q * PowerSeries.X ^ goodTotal n := by
  unfold goodDiagEval
  rw [MvPolynomial.eval₂Hom_monomial]
  rw [show n.prod (fun _ exponent => PowerSeries.X ^ exponent) =
      PowerSeries.X ^ n.sum (fun _ degree => degree) by
    unfold Finsupp.prod Finsupp.sum
    rw [Finset.prod_pow_eq_pow_sum]]
  rw [← goodTotal_eq_finsupp_sum]

theorem coeff_goodDiagEval (p : MvPolynomial (Fin 3) ℚ) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodDiagEval p) =
      ∑ n ∈ p.support.filter (fun n => goodTotal n = degree), p.coeff n := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  simp only [goodDiagEval_monomial, map_sum, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : goodTotal n = degree
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hd => h hd.symm)]

end FiniteDefects
