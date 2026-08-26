import FiniteDefects.D4GoodDiagonalImages

/-! # Diagonal form of the complete Good expansion -/

namespace FiniteDefects

open Finset BigOperators Finsupp

abbrev GoodTotalLe (degree : ℕ) :=
  {n : GoodIndex // goodTotal n ≤ degree}

abbrev GoodBoundBox (degree : ℕ) :=
  {p : ℕ × (ℕ × ℕ) //
    p ∈ goodBox (goodBound degree) ∧ p.1 + p.2.1 + p.2.2 ≤ degree}

noncomputable def goodBoundBoxEquivTotalLe (degree : ℕ) :
    GoodBoundBox degree ≃ GoodTotalLe degree where
  toFun := fun p => ⟨goodIndex p.1.1 p.1.2.1 p.1.2.2, by
    rw [goodTotal_coordinates]
    simpa using p.2.2⟩
  invFun := fun n => ⟨(n.1 0, (n.1 1, n.1 2)), by
    constructor
    · rw [goodBox_mem_iff]
      simp only [goodBound, goodIndex_zero, goodIndex_one, goodIndex_two]
      have htotal := n.2
      rw [goodTotal_coordinates] at htotal
      omega
    · rw [← goodTotal_coordinates]
      exact n.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    simp
  right_inv := by
    intro n
    apply Subtype.ext
    exact goodIndex_coordinates n.1

noncomputable def goodBoundBoxFintype (degree : ℕ) :
    Fintype (GoodBoundBox degree) := by
  let finiteCarrier := ↥(goodBox (goodBound degree))
  let constrained := {p : finiteCarrier //
    p.1.1 + p.1.2.1 + p.1.2.2 ≤ degree}
  letI : Fintype finiteCarrier := FinsetCoe.fintype _
  letI : Fintype constrained := inferInstance
  let equivalence : constrained ≃ GoodBoundBox degree :=
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  exact Fintype.ofEquiv constrained equivalence

noncomputable def goodTotalLeFintype (degree : ℕ) :
    Fintype (GoodTotalLe degree) := by
  letI := goodBoundBoxFintype degree
  exact Fintype.ofEquiv (GoodBoundBox degree)
    (goodBoundBoxEquivTotalLe degree)

noncomputable def goodAggregate (coefficients : GoodIndex → ℚ)
    (degree : ℕ) : ℚ := by
  letI := goodFiberFintype degree
  exact ∑ n : GoodFiber degree, coefficients n.1

noncomputable def goodAggregateSeries (coefficients : GoodIndex → ℚ) :
    PowerSeries ℚ :=
  PowerSeries.mk (goodAggregate coefficients)

@[simp] theorem coeff_goodAggregateSeries
    (coefficients : GoodIndex → ℚ) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodAggregateSeries coefficients) =
      goodAggregate coefficients degree := by
  simp [goodAggregateSeries]

noncomputable def goodTotalLeFiberEquiv (degree exponent : ℕ)
    (h : exponent ≤ degree) :
    {n : GoodTotalLe degree // goodTotal n.1 = exponent} ≃
      GoodFiber exponent where
  toFun := fun n => ⟨n.1.1, n.2⟩
  invFun := fun n => ⟨⟨n.1, by rw [n.2]; exact h⟩, n.2⟩
  left_inv := by intro n; rfl
  right_inv := by intro n; rfl

theorem sum_goodTotalLe_fiber (coefficients : GoodIndex → ℚ)
    (degree exponent : ℕ) (h : exponent ≤ degree) :
    letI := goodTotalLeFintype degree
    (∑ n ∈ (Finset.univ : Finset (GoodTotalLe degree)) with
        goodTotal n.1 = exponent, coefficients n.1) =
      goodAggregate coefficients exponent := by
  letI := goodTotalLeFintype degree
  letI := goodFiberFintype exponent
  let fiber := {n : GoodTotalLe degree // goodTotal n.1 = exponent}
  letI : Fintype fiber := inferInstance
  have hSubtype :
      (∑ n ∈ (Finset.univ : Finset (GoodTotalLe degree)) with
        goodTotal n.1 = exponent, coefficients n.1) =
        ∑ n : fiber, coefficients n.1.1 := by
    apply Finset.sum_subtype
      ((Finset.univ : Finset (GoodTotalLe degree)).filter
        (fun n => goodTotal n.1 = exponent))
    intro n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hSubtype]
  unfold goodAggregate
  apply Fintype.sum_equiv (goodTotalLeFiberEquiv degree exponent h)
  intro n
  rfl

theorem goodFiber_le_goodBound {degree : ℕ} (n : GoodFiber degree) :
    n.1 ≤ goodBound degree := by
  intro i
  have htotal := n.2
  rw [goodTotal_coordinates] at htotal
  fin_cases i <;> simp [goodBound] <;> omega

theorem coeff_goodDiagonal_expansion_eq_trunc
    (coefficients : GoodIndex → ℚ) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodDiagonal (goodExpansion coefficients)) =
      PowerSeries.coeff ℚ degree
        (goodDiagonal (goodTruncExpansion coefficients (goodBound degree))) := by
  letI := goodFiberFintype degree
  rw [coeff_goodDiagonal, coeff_goodDiagonal]
  apply Finset.sum_congr rfl
  intro n hn
  exact coeff_goodExpansion_eq_trunc coefficients
    (goodFiber_le_goodBound n)

theorem goodDiagonal_goodTruncExpansion (coefficients : GoodIndex → ℚ)
    (bound : GoodIndex) :
    goodDiagonal (goodTruncExpansion coefficients bound) =
      ∑ p ∈ goodBox bound,
        PowerSeries.C ℚ
            (coefficients (goodIndex p.1 p.2.1 p.2.2)) *
          goodQ ^ goodTotal (goodIndex p.1 p.2.1 p.2.2) := by
  change goodDiagonalRingHom (goodTruncExpansion coefficients bound) = _
  unfold goodTruncExpansion
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Algebra.smul_def, map_mul]
  change goodDiagonal (MvPowerSeries.C (Fin 3) ℚ
      (coefficients (goodIndex p.1 p.2.1 p.2.2))) *
      goodDiagonal (goodWPower (goodIndex p.1 p.2.1 p.2.2)) = _
  rw [goodDiagonal_C, goodDiagonal_goodWPower]

theorem coeff_goodDiagonal_expansion_eq_totalLe
    (coefficients : GoodIndex → ℚ) (degree : ℕ) :
    PowerSeries.coeff ℚ degree (goodDiagonal (goodExpansion coefficients)) =
      letI := goodTotalLeFintype degree
      ∑ n : GoodTotalLe degree,
        coefficients n.1 *
          PowerSeries.coeff ℚ degree (goodQ ^ goodTotal n.1) := by
  rw [coeff_goodDiagonal_expansion_eq_trunc]
  rw [goodDiagonal_goodTruncExpansion]
  simp only [map_sum, PowerSeries.coeff_C_mul]
  let term : ℕ × (ℕ × ℕ) → ℚ := fun p =>
    coefficients (goodIndex p.1 p.2.1 p.2.2) *
      PowerSeries.coeff ℚ degree
        (goodQ ^ goodTotal (goodIndex p.1 p.2.1 p.2.2))
  let bounded := (goodBox (goodBound degree)).filter
    (fun p => p.1 + p.2.1 + p.2.2 ≤ degree)
  have hfilter :
      (∑ p ∈ goodBox (goodBound degree), term p) =
        ∑ p ∈ bounded, term p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpBox hpBounded
    have hlarge : degree < p.1 + p.2.1 + p.2.2 := by
      simp only [bounded, Finset.mem_filter, not_and] at hpBounded
      have := hpBounded hpBox
      omega
    have htotal :
        goodTotal (goodIndex p.1 p.2.1 p.2.2) =
          p.1 + p.2.1 + p.2.2 := by
      rw [goodTotal_coordinates]
      simp only [goodIndex_zero, goodIndex_one, goodIndex_two]
    change term p = 0
    unfold term
    rw [coeff_pow_eq_zero_of_lt goodQ constantCoeff_goodQ]
    · simp
    · rw [htotal]
      exact hlarge
  rw [show (∑ p ∈ goodBox (goodBound degree),
      coefficients (goodIndex p.1 p.2.1 p.2.2) *
        PowerSeries.coeff ℚ degree
          (goodQ ^ goodTotal (goodIndex p.1 p.2.1 p.2.2))) =
      ∑ p ∈ goodBox (goodBound degree), term p by rfl]
  rw [hfilter]
  letI := goodBoundBoxFintype degree
  have hSubtype :
      (∑ p ∈ bounded, term p) =
        ∑ p : GoodBoundBox degree, term p.1 := by
    apply Finset.sum_subtype bounded
    intro p
    simp only [bounded, Finset.mem_filter]
  rw [hSubtype]
  letI := goodTotalLeFintype degree
  apply Fintype.sum_equiv (goodBoundBoxEquivTotalLe degree)
  intro p
  rfl

theorem goodDiagonal_goodExpansion (coefficients : GoodIndex → ℚ) :
    goodDiagonal (goodExpansion coefficients) =
      fpsCompose goodQ (goodAggregateSeries coefficients) := by
  ext degree
  rw [coeff_goodDiagonal_expansion_eq_totalLe]
  rw [coeff_fpsCompose]
  simp only [coeff_goodAggregateSeries]
  letI := goodTotalLeFintype degree
  let totalTerm : GoodTotalLe degree → ℚ := fun n =>
    coefficients n.1 *
      PowerSeries.coeff ℚ degree (goodQ ^ goodTotal n.1)
  calc
    (∑ n : GoodTotalLe degree, totalTerm n) =
        ∑ exponent ∈ Finset.range (degree + 1),
          ∑ n ∈ (Finset.univ : Finset (GoodTotalLe degree)) with
            goodTotal n.1 = exponent, totalTerm n := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro n hn
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le n.2
    _ = ∑ exponent ∈ Finset.range (degree + 1),
        goodAggregate coefficients exponent *
          PowerSeries.coeff ℚ degree (goodQ ^ exponent) := by
      apply Finset.sum_congr rfl
      intro exponent hexponent
      rw [← sum_goodTotalLe_fiber coefficients degree exponent
        (Nat.le_of_lt_succ (Finset.mem_range.mp hexponent))]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      have htotal := (Finset.mem_filter.mp hn).2
      simp only [totalTerm]
      rw [htotal]

end FiniteDefects
