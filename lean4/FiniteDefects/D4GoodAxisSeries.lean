import FiniteDefects.D4GoodMvDefinitions

/-! # One-axis binomial series inside the three-variable Good carrier -/

namespace FiniteDefects

open Finset BigOperators Finsupp

def goodAxisOnly (i : Fin 3) (n : GoodIndex) : Prop :=
  n = Finsupp.single i (n i)

noncomputable instance goodAxisOnlyDecidable (i : Fin 3) (n : GoodIndex) :
    Decidable (goodAxisOnly i n) := Classical.propDecidable _

def goodAxisCoefficient (energy degree : ℕ) : ℚ :=
  if energy = 0 then (-1 : ℚ) ^ degree else (energy - 1).choose degree

noncomputable def goodAxisSeries (i : Fin 3) (energy : ℕ) : GoodSeries :=
  fun n => if goodAxisOnly i n then goodAxisCoefficient energy (n i) else 0

@[simp] theorem coeff_goodAxisSeries (i : Fin 3) (energy : ℕ)
    (n : GoodIndex) :
    MvPowerSeries.coeff ℚ n (goodAxisSeries i energy) =
      if goodAxisOnly i n then goodAxisCoefficient energy (n i) else 0 := by
  rfl

theorem goodAxisOnly_zero (i : Fin 3) : goodAxisOnly i 0 := by
  simp [goodAxisOnly]

theorem coeff_goodX_mul (i : Fin 3) (f : GoodSeries) (n : GoodIndex) :
    MvPowerSeries.coeff ℚ n (MvPowerSeries.X i * f) =
      if Finsupp.single i 1 ≤ n then
        MvPowerSeries.coeff ℚ (n - Finsupp.single i 1) f else 0 := by
  rw [show MvPowerSeries.X i =
      MvPowerSeries.monomial ℚ (Finsupp.single i 1) 1 by rfl,
    MvPowerSeries.coeff_monomial_mul]
  split_ifs <;> simp

theorem coeff_mul_goodX (i : Fin 3) (f : GoodSeries) (n : GoodIndex) :
    MvPowerSeries.coeff ℚ n (f * MvPowerSeries.X i) =
      if Finsupp.single i 1 ≤ n then
        MvPowerSeries.coeff ℚ (n - Finsupp.single i 1) f else 0 := by
  rw [show MvPowerSeries.X i =
      MvPowerSeries.monomial ℚ (Finsupp.single i 1) 1 by rfl,
    MvPowerSeries.coeff_mul_monomial]
  split_ifs <;> simp

theorem goodAxisOnly_sub_iff (i : Fin 3) (n : GoodIndex)
    (hle : Finsupp.single i 1 ≤ n) :
    goodAxisOnly i (n - Finsupp.single i 1) ↔ goodAxisOnly i n := by
  constructor
  · intro hsub
    unfold goodAxisOnly at hsub ⊢
    rw [← tsub_add_cancel_of_le hle, hsub]
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.coe_tsub, Nat.sub_add_cancel
        (Finsupp.single_le_iff.mp hle)]
    · simp [Finsupp.coe_tsub, hji]
  · intro hn
    unfold goodAxisOnly at hn ⊢
    rw [hn]
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.coe_tsub]
    · simp [Finsupp.coe_tsub, hji]

theorem goodAxis_sub_coord (i : Fin 3) (n : GoodIndex) :
    (n - Finsupp.single i 1 : GoodIndex) i = n i - 1 := by
  simp [Finsupp.coe_tsub]

@[simp] theorem constantCoeff_goodAxisSeries (i : Fin 3) (energy : ℕ) :
    MvPowerSeries.constantCoeff (Fin 3) ℚ (goodAxisSeries i energy) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_goodAxisSeries, if_pos (goodAxisOnly_zero i)]
  simp [goodAxisCoefficient]

theorem goodAxisCoefficient_succ (energy degree : ℕ) :
    goodAxisCoefficient (energy + 1) degree = energy.choose degree := by
  simp [goodAxisCoefficient]

theorem goodAxisCoefficient_zero (degree : ℕ) :
    goodAxisCoefficient 0 degree = (-1 : ℚ) ^ degree := by
  simp [goodAxisCoefficient]

theorem goodAxisSeries_zero_mul (i : Fin 3) :
    goodOnePlus i * goodAxisSeries i 0 = 1 := by
  ext n
  rw [show goodOnePlus i = 1 + MvPowerSeries.X i by rfl,
    add_mul, one_mul, map_add]
  by_cases hn : n = 0
  · subst n
    rw [coeff_goodAxisSeries, if_pos (goodAxisOnly_zero i)]
    simp [goodAxisCoefficient]
  · by_cases haxis : goodAxisOnly i n
    · have hpositive : 0 < n i := by
        by_contra hzero
        have : n i = 0 := by omega
        exact hn (haxis.trans (by simp [this]))
      have hsingle : Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact hpositive
      rw [coeff_goodX_mul, if_pos hsingle]
      simp only [one_mul,
        coeff_goodAxisSeries, haxis, if_true, goodAxisCoefficient_zero]
      have haxisSub := (goodAxisOnly_sub_iff i n hsingle).2 haxis
      have hcoord := goodAxis_sub_coord i n
      rw [if_pos haxisSub, hcoord]
      have hsucc : n i - 1 + 1 = n i := by omega
      rw [← hsucc, pow_succ]
      rw [MvPowerSeries.coeff_one, if_neg hn]
      rw [Nat.add_sub_cancel]
      ring
    · have hnotle : ¬Finsupp.single i 1 ≤ n ∨
          ¬goodAxisOnly i (n - Finsupp.single i 1) := by
        by_cases hle : Finsupp.single i 1 ≤ n
        · right
          exact fun hsub => haxis ((goodAxisOnly_sub_iff i n hle).1 hsub)
        · exact Or.inl hle
      rw [coeff_goodAxisSeries, if_neg haxis]
      rcases hnotle with hnotle | hnotaxis
      · rw [coeff_goodX_mul, if_neg hnotle]
        simp [MvPowerSeries.coeff_one, hn]
      · rw [coeff_goodX_mul]
        split_ifs with hle
        · simp [hnotaxis, MvPowerSeries.coeff_one, hn]
        · simp [MvPowerSeries.coeff_one, hn]

theorem goodOnePlus_pow_coeff (i : Fin 3) (energy : ℕ) (n : GoodIndex) :
    MvPowerSeries.coeff ℚ n (goodOnePlus i ^ energy) =
      if goodAxisOnly i n then ((energy.choose (n i) : ℕ) : ℚ) else 0 := by
  induction energy generalizing n with
  | zero =>
      by_cases hn : n = 0
      · subst n
        simp [goodAxisOnly]
      · simp only [pow_zero, MvPowerSeries.coeff_one, if_neg hn]
        by_cases haxis : goodAxisOnly i n
        · rw [if_pos haxis]
          have hpositive : 0 < n i := by
            by_contra hzero
            have : n i = 0 := by omega
            exact hn (haxis.trans (by simp [this]))
          simp [Nat.choose_eq_zero_of_lt hpositive]
        · rw [if_neg haxis]
  | succ energy ih =>
      rw [pow_succ]
      nth_rw 2 [show goodOnePlus i = 1 + MvPowerSeries.X i by rfl]
      rw [mul_add, mul_one, map_add, ih]
      by_cases haxis : goodAxisOnly i n
      · simp only [if_pos haxis]
        by_cases hzero : n i = 0
        · have hn : n = 0 := haxis.trans (by simp [hzero])
          subst n
          simp [goodAxisOnly]
        · have hle : Finsupp.single i 1 ≤ n := by
            rw [Finsupp.single_le_iff]
            omega
          rw [coeff_mul_goodX, if_pos hle]
          have haxisSub := (goodAxisOnly_sub_iff i n hle).2 haxis
          rw [ih, if_pos haxisSub]
          have hcoord := goodAxis_sub_coord i n
          rw [hcoord]
          have hsucc : n i - 1 + 1 = n i :=
            Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
          rw [← hsucc]
          rw [Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one, Nat.add_comm,
            Nat.add_sub_cancel_left]
          push_cast
          ring
      · rw [if_neg haxis]
        have hnotle : ¬Finsupp.single i 1 ≤ n ∨
            ¬goodAxisOnly i (n - Finsupp.single i 1) := by
          by_cases hle : Finsupp.single i 1 ≤ n
          · right
            exact fun hsub => haxis ((goodAxisOnly_sub_iff i n hle).1 hsub)
          · exact Or.inl hle
        rcases hnotle with hnotle | hnotaxis
        · rw [coeff_mul_goodX, if_neg hnotle]
          simp [haxis]
        · rw [coeff_mul_goodX]
          split_ifs with hle
          · rw [ih, if_neg hnotaxis]
            simp
          · simp

theorem goodOnePlus_mul_axisSeries (i : Fin 3) (energy : ℕ) :
    goodOnePlus i * goodAxisSeries i (energy + 1) =
      goodOnePlus i ^ (energy + 1) := by
  ext n
  rw [show goodOnePlus i * goodAxisSeries i (energy + 1) =
      goodAxisSeries i (energy + 1) +
        MvPowerSeries.X i * goodAxisSeries i (energy + 1) by
          unfold goodOnePlus
          ring]
  rw [map_add, coeff_goodX_mul, goodOnePlus_pow_coeff]
  by_cases haxis : goodAxisOnly i n
  · simp only [coeff_goodAxisSeries, if_pos haxis,
      goodAxisCoefficient_succ]
    by_cases hzero : n i = 0
    · have hn : n = 0 := haxis.trans (by simp [hzero])
      subst n
      simp [goodAxisOnly]
    · have hle : Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        omega
      rw [if_pos hle]
      have haxisSub := (goodAxisOnly_sub_iff i n hle).2 haxis
      rw [if_pos haxisSub]
      have hcoord := goodAxis_sub_coord i n
      rw [hcoord]
      have hsucc : n i - 1 + 1 = n i :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
      rw [← hsucc]
      rw [Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one, Nat.add_comm,
        Nat.add_sub_cancel_left]
      push_cast
      ring
  · rw [coeff_goodAxisSeries, if_neg haxis, if_neg haxis]
    have hnotle : ¬Finsupp.single i 1 ≤ n ∨
        ¬goodAxisOnly i (n - Finsupp.single i 1) := by
      by_cases hle : Finsupp.single i 1 ≤ n
      · right
        exact fun hsub => haxis ((goodAxisOnly_sub_iff i n hle).1 hsub)
      · exact Or.inl hle
    rcases hnotle with hnotle | hnotaxis
    · rw [if_neg hnotle]
      simp
    · split_ifs with hle
      · simp [hnotaxis]
      · simp

theorem goodAxisSeries_eq (i : Fin 3) (energy : ℕ) :
    goodAxisSeries i energy = goodOnePlus i ^ energy * (goodOnePlus i)⁻¹ := by
  apply mul_left_cancel₀ (show goodOnePlus i ≠ 0 by
    intro hzero
    have := congrArg (MvPowerSeries.constantCoeff (Fin 3) ℚ) hzero
    simp at this)
  rcases energy with _ | energy
  · rw [goodAxisSeries_zero_mul]
    simp only [pow_zero, one_mul]
    exact (MvPowerSeries.mul_inv_cancel (goodOnePlus i) (by simp)).symm
  · rw [goodOnePlus_mul_axisSeries]
    calc
      goodOnePlus i ^ (energy + 1) =
          goodOnePlus i ^ (energy + 1) *
            (goodOnePlus i * (goodOnePlus i)⁻¹) := by
              rw [MvPowerSeries.mul_inv_cancel (goodOnePlus i) (by simp), mul_one]
      _ = goodOnePlus i *
          (goodOnePlus i ^ (energy + 1) * (goodOnePlus i)⁻¹) := by ring

theorem goodAxisSeries_succ_eq_pow (i : Fin 3) (energy : ℕ) :
    goodAxisSeries i (energy + 1) = goodOnePlus i ^ energy := by
  rw [goodAxisSeries_eq]
  calc
    goodOnePlus i ^ (energy + 1) * (goodOnePlus i)⁻¹ =
        goodOnePlus i ^ energy *
          (goodOnePlus i * (goodOnePlus i)⁻¹) := by
            rw [pow_succ]
            ring
    _ = goodOnePlus i ^ energy := by
      rw [MvPowerSeries.mul_inv_cancel (goodOnePlus i) (by simp), mul_one]

end FiniteDefects
