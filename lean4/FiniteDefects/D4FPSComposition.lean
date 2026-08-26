import FiniteDefects.D4GoodMvDefinitions
import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Minimal univariate formal-series composition used by the Good proof -/

namespace FiniteDefects

open Finset

noncomputable def fpsCompose (g f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ∑ degree ∈ Finset.range (n + 1),
      PowerSeries.coeff ℚ degree f * PowerSeries.coeff ℚ n (g ^ degree)

@[simp] theorem coeff_fpsCompose (g f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff ℚ n (fpsCompose g f) =
      ∑ degree ∈ Finset.range (n + 1),
        PowerSeries.coeff ℚ degree f *
          PowerSeries.coeff ℚ n (g ^ degree) := by
  simp [fpsCompose]

theorem fpsCompose_constantCoeff (g f : PowerSeries ℚ) :
    PowerSeries.constantCoeff ℚ (fpsCompose g f) =
      PowerSeries.constantCoeff ℚ f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [fpsCompose]

@[simp] theorem fpsCompose_zero (g : PowerSeries ℚ) :
    fpsCompose g 0 = 0 := by
  ext n
  simp [fpsCompose]

@[simp] theorem fpsCompose_add (g f h : PowerSeries ℚ) :
    fpsCompose g (f + h) = fpsCompose g f + fpsCompose g h := by
  ext n
  simp only [coeff_fpsCompose, map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro degree hdegree
  ring

@[simp] theorem fpsCompose_C (g : PowerSeries ℚ) (q : ℚ) :
    fpsCompose g (PowerSeries.C ℚ q) = PowerSeries.C ℚ q := by
  ext n
  simp only [coeff_fpsCompose, PowerSeries.coeff_C]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro degree hdegree hne
    simp [hne]
  · simp

theorem fpsCompose_X (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0) :
    fpsCompose g PowerSeries.X = g := by
  ext n
  rcases n with _ | n
  · simp [fpsCompose, hg]
  · simp only [coeff_fpsCompose, PowerSeries.coeff_X]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro degree hdegree hne
      simp [hne]
    · simp

@[simp] theorem fpsCompose_X_left (f : PowerSeries ℚ) :
    fpsCompose PowerSeries.X f = f := by
  ext degree
  rw [coeff_fpsCompose]
  rw [Finset.sum_eq_single degree]
  · rw [PowerSeries.coeff_X_pow_self, mul_one]
  · intro exponent hexponent hne
    rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hne), mul_zero]
  · simp

@[simp] theorem fpsCompose_one (g : PowerSeries ℚ) :
    fpsCompose g 1 = 1 := by
  rw [show (1 : PowerSeries ℚ) = PowerSeries.C ℚ 1 by rfl]
  exact fpsCompose_C g 1

@[simp] theorem fpsCompose_natCast (g : PowerSeries ℚ) (n : ℕ) :
    fpsCompose g n = n := by
  rw [show (n : PowerSeries ℚ) = PowerSeries.C ℚ n by rfl]
  exact fpsCompose_C g n

theorem coeff_pow_eq_zero_of_lt (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0) {degree exponent : ℕ}
    (h : degree < exponent) :
    PowerSeries.coeff ℚ degree (g ^ exponent) = 0 := by
  have hX : PowerSeries.X ∣ g := PowerSeries.X_dvd_iff.mpr hg
  have hpow : PowerSeries.X ^ exponent ∣ g ^ exponent :=
    pow_dvd_pow_of_dvd hX exponent
  exact (PowerSeries.X_pow_dvd_iff.mp hpow) degree h

theorem coeff_fpsCompose_eq_eval_trunc (g f : PowerSeries ℚ) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (fpsCompose g f) =
      PowerSeries.coeff ℚ degree
        ((PowerSeries.trunc (degree + 1) f).eval₂
          (PowerSeries.C ℚ) g) := by
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [coeff_fpsCompose, map_sum, PowerSeries.coeff_C_mul]

theorem coeff_eval₂_eq_range (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0)
    (p : Polynomial ℚ) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (p.eval₂ (PowerSeries.C ℚ) g) =
      ∑ exponent ∈ Finset.range (degree + 1),
        p.coeff exponent * PowerSeries.coeff ℚ degree (g ^ exponent) := by
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum, map_sum, PowerSeries.coeff_C_mul]
  let term : ℕ → ℚ := fun exponent =>
    p.coeff exponent * PowerSeries.coeff ℚ degree (g ^ exponent)
  let small := p.support.filter (fun exponent => exponent < degree + 1)
  calc
    (∑ exponent ∈ p.support, term exponent) =
        ∑ exponent ∈ small, term exponent := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro exponent hsupp hnsmall
      have hlarge : degree < exponent := by
        simp only [small, Finset.mem_filter, not_and] at hnsmall
        have := hnsmall hsupp
        omega
      simp [term, coeff_pow_eq_zero_of_lt g hg hlarge]
    _ = ∑ exponent ∈ Finset.range (degree + 1), term exponent := by
      apply Finset.sum_subset
      · intro exponent hexponent
        simp only [small, Finset.mem_filter, Finset.mem_range] at hexponent ⊢
        exact hexponent.2
      · intro exponent hrange hnsmall
        have hnSupport : exponent ∉ p.support := by
          intro hsupp
          apply hnsmall
          simp only [small, Finset.mem_filter]
          exact ⟨hsupp, Finset.mem_range.mp hrange⟩
        simp [term, Polynomial.not_mem_support_iff.mp hnSupport]
    _ = ∑ exponent ∈ Finset.range (degree + 1),
        p.coeff exponent * PowerSeries.coeff ℚ degree (g ^ exponent) := rfl

theorem coeff_eval₂_trunc_bound_of_le (g f : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0)
    {small large : ℕ} (h : small ≤ large) :
    PowerSeries.coeff ℚ small
        ((PowerSeries.trunc (large + 1) f).eval₂ (PowerSeries.C ℚ) g) =
      PowerSeries.coeff ℚ small (fpsCompose g f) := by
  rw [coeff_eval₂_eq_range g hg]
  rw [coeff_fpsCompose]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  rw [PowerSeries.coeff_trunc, if_pos]
  exact (Finset.mem_range.mp hexponent).trans_le (Nat.succ_le_succ h)

theorem coeff_eval₂_trunc_coe (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0)
    (p : Polynomial ℚ) (degree : ℕ) :
    PowerSeries.coeff ℚ degree
        ((PowerSeries.trunc (degree + 1) (p : PowerSeries ℚ)).eval₂
          (PowerSeries.C ℚ) g) =
      PowerSeries.coeff ℚ degree (p.eval₂ (PowerSeries.C ℚ) g) := by
  rw [coeff_eval₂_eq_range g hg, coeff_eval₂_eq_range g hg]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  rw [PowerSeries.coeff_trunc, if_pos (Finset.mem_range.mp hexponent),
    Polynomial.coeff_coe]

@[simp] theorem fpsCompose_mul (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0)
    (f h : PowerSeries ℚ) :
    fpsCompose g (f * h) = fpsCompose g f * fpsCompose g h := by
  ext degree
  calc
    PowerSeries.coeff ℚ degree (fpsCompose g (f * h)) =
        PowerSeries.coeff ℚ degree
          ((PowerSeries.trunc (degree + 1) (f * h)).eval₂
            (PowerSeries.C ℚ) g) :=
      coeff_fpsCompose_eq_eval_trunc g (f * h) degree
    _ = PowerSeries.coeff ℚ degree
          ((PowerSeries.trunc (degree + 1)
            (((PowerSeries.trunc (degree + 1) f : Polynomial ℚ) :
                PowerSeries ℚ) *
              ((PowerSeries.trunc (degree + 1) h : Polynomial ℚ) :
                PowerSeries ℚ))).eval₂ (PowerSeries.C ℚ) g) := by
      rw [PowerSeries.trunc_trunc_mul_trunc]
    _ = PowerSeries.coeff ℚ degree
          (((PowerSeries.trunc (degree + 1) f) *
            (PowerSeries.trunc (degree + 1) h)).eval₂
              (PowerSeries.C ℚ) g) := by
      simpa only [Polynomial.coe_mul] using
        (coeff_eval₂_trunc_coe g hg
          ((PowerSeries.trunc (degree + 1) f) *
            (PowerSeries.trunc (degree + 1) h)) degree)
    _ = PowerSeries.coeff ℚ degree
          ((PowerSeries.trunc (degree + 1) f).eval₂
              (PowerSeries.C ℚ) g *
            (PowerSeries.trunc (degree + 1) h).eval₂
              (PowerSeries.C ℚ) g) := by
      rw [Polynomial.eval₂_mul]
    _ = PowerSeries.coeff ℚ degree
          (fpsCompose g f * fpsCompose g h) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro pair hpair
      have hsum := Finset.mem_antidiagonal.mp hpair
      rw [coeff_eval₂_trunc_bound_of_le g f hg (by omega),
        coeff_eval₂_trunc_bound_of_le g h hg (by omega)]

noncomputable def fpsComposeRingHom (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0) :
    PowerSeries ℚ →+* PowerSeries ℚ where
  toFun := fpsCompose g
  map_zero' := fpsCompose_zero g
  map_one' := fpsCompose_one g
  map_add' := fpsCompose_add g
  map_mul' := fpsCompose_mul g hg

@[simp] theorem fpsComposeRingHom_X (g : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0) :
    fpsComposeRingHom g hg PowerSeries.X = g :=
  fpsCompose_X g hg

@[simp] theorem fpsCompose_pow (g f : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0) (exponent : ℕ) :
    fpsCompose g (f ^ exponent) = fpsCompose g f ^ exponent := by
  exact map_pow (fpsComposeRingHom g hg) f exponent

theorem fpsCompose_inv (g f : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0)
    (hf : PowerSeries.constantCoeff ℚ f ≠ 0) :
    fpsCompose g f⁻¹ = (fpsCompose g f)⁻¹ := by
  have hmap : PowerSeries.constantCoeff ℚ (fpsCompose g f) ≠ 0 := by
    rw [fpsCompose_constantCoeff]
    exact hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one hmap]
  rw [← fpsCompose_mul g hg, PowerSeries.inv_mul_cancel f hf,
    fpsCompose_one]

theorem fpsCompose_assoc (g h f : PowerSeries ℚ)
    (hg : PowerSeries.constantCoeff ℚ g = 0)
    (hh : PowerSeries.constantCoeff ℚ h = 0) :
    fpsCompose g (fpsCompose h f) = fpsCompose (fpsCompose g h) f := by
  ext degree
  rw [coeff_fpsCompose, coeff_fpsCompose]
  calc
    (∑ middle ∈ Finset.range (degree + 1),
      PowerSeries.coeff ℚ middle (fpsCompose h f) *
        PowerSeries.coeff ℚ degree (g ^ middle)) =
      ∑ middle ∈ Finset.range (degree + 1),
        (∑ exponent ∈ Finset.range (degree + 1),
          PowerSeries.coeff ℚ exponent f *
            PowerSeries.coeff ℚ middle (h ^ exponent)) *
          PowerSeries.coeff ℚ degree (g ^ middle) := by
      apply Finset.sum_congr rfl
      intro middle hmiddle
      apply congrArg (fun q => q * PowerSeries.coeff ℚ degree (g ^ middle))
      rw [coeff_fpsCompose]
      apply Finset.sum_subset
      · exact Finset.range_mono (Finset.mem_range.mp hmiddle)
      · intro exponent hexponent hsmall
        have hlt : middle < exponent := by
          rw [Finset.mem_range] at hexponent
          rw [Finset.mem_range] at hsmall
          omega
        rw [coeff_pow_eq_zero_of_lt h hh hlt, mul_zero]
    _ = ∑ exponent ∈ Finset.range (degree + 1),
        PowerSeries.coeff ℚ exponent f *
          (∑ middle ∈ Finset.range (degree + 1),
            PowerSeries.coeff ℚ middle (h ^ exponent) *
              PowerSeries.coeff ℚ degree (g ^ middle)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro exponent hexponent
      apply Finset.sum_congr rfl
      intro middle hmiddle
      ring
    _ = ∑ exponent ∈ Finset.range (degree + 1),
        PowerSeries.coeff ℚ exponent f *
          PowerSeries.coeff ℚ degree ((fpsCompose g h) ^ exponent) := by
      apply Finset.sum_congr rfl
      intro exponent hexponent
      apply congrArg (fun q => PowerSeries.coeff ℚ exponent f * q)
      rw [← coeff_fpsCompose]
      rw [fpsCompose_pow g h hg]

@[simp] theorem fpsCompose_sub (g f h : PowerSeries ℚ) :
    fpsCompose g (f - h) = fpsCompose g f - fpsCompose g h := by
  rw [sub_eq_add_neg, sub_eq_add_neg, fpsCompose_add]
  congr 1
  ext n
  simp [fpsCompose]

end FiniteDefects
