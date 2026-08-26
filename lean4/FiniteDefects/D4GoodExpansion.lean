import FiniteDefects.D4GoodDuality

/-! # Completeness of the specialized Good w-monomial basis -/

namespace FiniteDefects

open Finset BigOperators Finsupp

noncomputable def goodTruncExpansion (coefficients : GoodIndex → ℚ)
    (bound : GoodIndex) : GoodSeries :=
  ∑ p ∈ goodBox bound,
    coefficients (goodIndex p.1 p.2.1 p.2.2) •
      goodWPower (goodIndex p.1 p.2.1 p.2.2)

theorem goodBox_mem_iff (bound : GoodIndex) (p : ℕ × (ℕ × ℕ)) :
    p ∈ goodBox bound ↔
      p.1 ≤ bound 0 ∧ p.2.1 ≤ bound 1 ∧ p.2.2 ≤ bound 2 := by
  simp [goodBox]
  omega

theorem goodBox_mono {lower upper : GoodIndex} (h : lower ≤ upper) :
    goodBox lower ⊆ goodBox upper := by
  intro p hp
  rw [goodBox_mem_iff] at hp ⊢
  exact ⟨hp.1.trans (h 0), hp.2.1.trans (h 1), hp.2.2.trans (h 2)⟩

@[simp] theorem coeff_goodTruncExpansion
    (coefficients : GoodIndex → ℚ) (bound m : GoodIndex) :
    MvPowerSeries.coeff ℚ m (goodTruncExpansion coefficients bound) =
      ∑ p ∈ goodBox bound,
        coefficients (goodIndex p.1 p.2.1 p.2.2) *
          MvPowerSeries.coeff ℚ m
            (goodWPower (goodIndex p.1 p.2.1 p.2.2)) := by
  simp [goodTruncExpansion, Finset.smul_sum]

@[simp] theorem coeff_goodExpansion
    (coefficients : GoodIndex → ℚ) (m : GoodIndex) :
    MvPowerSeries.coeff ℚ m (goodExpansion coefficients) =
      ∑ p ∈ goodBox m,
        coefficients (goodIndex p.1 p.2.1 p.2.2) *
          MvPowerSeries.coeff ℚ m
            (goodWPower (goodIndex p.1 p.2.1 p.2.2)) := by
  rfl

theorem coeff_goodExpansion_eq_trunc
    (coefficients : GoodIndex → ℚ) {m bound : GoodIndex} (hmb : m ≤ bound) :
    MvPowerSeries.coeff ℚ m (goodExpansion coefficients) =
      MvPowerSeries.coeff ℚ m (goodTruncExpansion coefficients bound) := by
  rw [coeff_goodExpansion, coeff_goodTruncExpansion]
  apply Finset.sum_subset (goodBox_mono hmb)
  intro p hpBound hpNotSmall
  have hnotle : ¬goodIndex p.1 p.2.1 p.2.2 ≤ m := by
    intro hle
    apply hpNotSmall
    rw [goodBox_mem_iff]
    exact ⟨by simpa using hle 0, by simpa using hle 1,
      by simpa using hle 2⟩
  rw [goodWPower_coeff_zero_of_not_le hnotle, mul_zero]

theorem goodFunctional_eq_coeff_kernel (n : GoodIndex) (f : GoodSeries) :
    goodFunctional n f = MvPowerSeries.coeff ℚ n
      (f * (goodPhiPower n * goodDeterminant)) := by
  unfold goodFunctional
  congr 1
  ring

@[simp] theorem goodFunctional_add (n : GoodIndex) (f g : GoodSeries) :
    goodFunctional n (f + g) = goodFunctional n f + goodFunctional n g := by
  unfold goodFunctional
  rw [add_mul, add_mul, map_add]

@[simp] theorem goodFunctional_smul (n : GoodIndex) (q : ℚ)
    (f : GoodSeries) :
    goodFunctional n (q • f) = q * goodFunctional n f := by
  unfold goodFunctional
  rw [smul_mul_assoc, smul_mul_assoc, map_smul]
  rfl

theorem goodFunctional_sum {ι : Type*} (n : GoodIndex) (s : Finset ι)
    (f : ι → GoodSeries) :
    goodFunctional n (∑ i ∈ s, f i) = ∑ i ∈ s, goodFunctional n (f i) := by
  unfold goodFunctional
  simp only [Finset.sum_mul, map_sum]

theorem goodFunctional_expansion (coefficients : GoodIndex → ℚ)
    (n : GoodIndex) :
    goodFunctional n (goodExpansion coefficients) = coefficients n := by
  rw [goodFunctional_eq_coeff_kernel]
  rw [MvPowerSeries.coeff_mul]
  calc
    (∑ pair ∈ Finset.antidiagonal n,
      MvPowerSeries.coeff ℚ pair.1 (goodExpansion coefficients) *
        MvPowerSeries.coeff ℚ pair.2
          (goodPhiPower n * goodDeterminant)) =
        ∑ pair ∈ Finset.antidiagonal n,
          MvPowerSeries.coeff ℚ pair.1
              (goodTruncExpansion coefficients n) *
            MvPowerSeries.coeff ℚ pair.2
              (goodPhiPower n * goodDeterminant) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      apply congrArg (fun q => q * MvPowerSeries.coeff ℚ pair.2
        (goodPhiPower n * goodDeterminant))
      apply coeff_goodExpansion_eq_trunc
      have hsum := Finset.mem_antidiagonal.mp hpair
      intro i
      have hi := congrArg (fun index : GoodIndex => index i) hsum
      simp at hi
      omega
    _ = MvPowerSeries.coeff ℚ n
          (goodTruncExpansion coefficients n *
            (goodPhiPower n * goodDeterminant)) := by
      rw [MvPowerSeries.coeff_mul]
    _ = goodFunctional n (goodTruncExpansion coefficients n) := by
      rw [goodFunctional_eq_coeff_kernel]
    _ = ∑ p ∈ goodBox n,
        coefficients (goodIndex p.1 p.2.1 p.2.2) *
          goodFunctional n (goodWPower (goodIndex p.1 p.2.1 p.2.2)) := by
      unfold goodTruncExpansion
      rw [goodFunctional_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [goodFunctional_smul]
    _ = coefficients n := by
      rw [show ∑ p ∈ goodBox n,
        coefficients (goodIndex p.1 p.2.1 p.2.2) *
          goodFunctional n (goodWPower (goodIndex p.1 p.2.1 p.2.2)) =
        coefficients n by
      rw [show n = goodIndex (n 0) (n 1) (n 2) by
        exact (goodIndex_coordinates n).symm]
      rw [Finset.sum_eq_single (n 0, (n 1, n 2))]
      · simp [goodFunctional_wPower]
      · intro p hp hne
        rw [goodFunctional_wPower, if_neg]
        · simp
        · intro heq
          apply hne
          have h0 := congrArg (fun index : GoodIndex => index 0) heq
          have h1 := congrArg (fun index : GoodIndex => index 1) heq
          have h2 := congrArg (fun index : GoodIndex => index 2) heq
          simpa using Prod.ext (by simpa using h0)
            (Prod.ext (by simpa using h1) (by simpa using h2))
      · rw [goodBox_mem_iff]
        simp]

theorem goodTotal_eq_zero_iff (n : GoodIndex) : goodTotal n = 0 ↔ n = 0 := by
  rw [goodTotal_coordinates]
  constructor
  · intro h
    apply Finsupp.ext
    intro i
    fin_cases i
    · have h0 : n 0 = 0 := by omega
      simpa using h0
    · have h1 : n 1 = 0 := by omega
      simpa using h1
    · have h2 : n 2 = 0 := by omega
      simpa using h2
  · rintro rfl
    simp [goodTotal]

theorem goodFunctional_injective : Function.Injective
    (fun f : GoodSeries => fun n => goodFunctional n f) := by
  intro f g hfg
  apply MvPowerSeries.ext
  intro n
  have aux : ∀ degree : ℕ, ∀ index : GoodIndex,
      goodTotal index = degree →
      MvPowerSeries.coeff ℚ index f = MvPowerSeries.coeff ℚ index g := by
    intro degree
    induction degree using Nat.strong_induction_on with
    | h degree ih =>
        intro index hdegree
        have hL := congrFun hfg index
        change goodFunctional index f = goodFunctional index g at hL
        rw [goodFunctional_eq_coeff_kernel,
          goodFunctional_eq_coeff_kernel,
          MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul] at hL
        let target : GoodIndex × GoodIndex := (index, 0)
        have htarget : target ∈ Finset.antidiagonal index := by
          simp [target]
        rw [Finset.sum_eq_add_sum_diff_singleton htarget,
          Finset.sum_eq_add_sum_diff_singleton htarget] at hL
        have hrest :
            (∑ pair ∈ (Finset.antidiagonal index).erase target,
              MvPowerSeries.coeff ℚ pair.1 f *
                MvPowerSeries.coeff ℚ pair.2
                  (goodPhiPower index * goodDeterminant)) =
            ∑ pair ∈ (Finset.antidiagonal index).erase target,
              MvPowerSeries.coeff ℚ pair.1 g *
                MvPowerSeries.coeff ℚ pair.2
                  (goodPhiPower index * goodDeterminant) := by
          apply Finset.sum_congr rfl
          intro pair hpair
          have hmem := Finset.mem_of_mem_erase hpair
          have hne := (Finset.mem_erase.mp hpair).1
          apply congrArg (fun q => q *
            MvPowerSeries.coeff ℚ pair.2
              (goodPhiPower index * goodDeterminant))
          apply ih (goodTotal pair.1)
          · have hsum := Finset.mem_antidiagonal.mp hmem
            have htotal := congrArg goodTotal hsum
            rw [goodTotal_add, hdegree] at htotal
            have hsecond : 0 < goodTotal pair.2 := by
              by_contra hz
              have hz0 : goodTotal pair.2 = 0 := by omega
              have hp2 := (goodTotal_eq_zero_iff pair.2).mp hz0
              have hp1 : pair.1 = index := by
                rw [← hsum, hp2, add_zero]
              exact hne (Prod.ext hp1 hp2)
            omega
          · rfl
        dsimp [target] at hL
        dsimp [target] at hrest
        have hconstant :
            MvPowerSeries.constantCoeff (Fin 3) ℚ
              (goodPhiPower index * goodDeterminant) = 1 := by simp
        rw [hconstant, mul_one, mul_one] at hL
        rw [← Finset.sdiff_singleton_eq_erase] at hrest
        rw [hrest] at hL
        exact add_right_cancel hL
  exact aux (goodTotal n) n rfl

theorem goodExpansion_functional (f : GoodSeries) :
    goodExpansion (fun n => goodFunctional n f) = f := by
  apply goodFunctional_injective
  funext n
  change goodFunctional n (goodExpansion fun n => goodFunctional n f) =
    goodFunctional n f
  rw [goodFunctional_expansion]

end FiniteDefects
