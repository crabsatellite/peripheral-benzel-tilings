import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Uniqueness and cyclic symmetry of the Lagrange--Good small root
-/

namespace BenzelProblem6Kernel

open PowerSeries

theorem coeff_mul_congr_of_le {R : Type*} [CommSemiring R]
    {left₀ right₀ left₁ right₁ : R⟦X⟧} (degree : ℕ)
    (h₀ : ∀ k ≤ degree, coeff R k left₀ = coeff R k right₀)
    (h₁ : ∀ k ≤ degree, coeff R k left₁ = coeff R k right₁) :
    coeff R degree (left₀ * left₁) =
      coeff R degree (right₀ * right₁) := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hsum := Finset.mem_antidiagonal.mp hij
  rw [h₀ i (by omega), h₁ j (by omega)]

theorem coeff_one_add_congr_of_le {R : Type*} [CommSemiring R]
    {left right : R⟦X⟧} (degree : ℕ)
    (h : ∀ k ≤ degree, coeff R k left = coeff R k right) :
    coeff R degree (1 + left) = coeff R degree (1 + right) := by
  simp [h degree]

theorem coeff_goodPhi_congr_of_le
    {left₀ right₀ left₁ right₁ : ℚ⟦X⟧} (degree : ℕ)
    (h₀ : ∀ k ≤ degree, coeff ℚ k left₀ = coeff ℚ k right₀)
    (h₁ : ∀ k ≤ degree, coeff ℚ k left₁ = coeff ℚ k right₁) :
    coeff ℚ degree ((1 + left₀) ^ 2 * (1 + left₁)) =
      coeff ℚ degree ((1 + right₀) ^ 2 * (1 + right₁)) := by
  apply coeff_mul_congr_of_le degree
  · intro k hk
    simp only [pow_two]
    apply coeff_mul_congr_of_le k <;>
      intro j hj <;>
      exact coeff_one_add_congr_of_le j
        (fun q hq => h₀ q ((hq.trans hj).trans hk))
  · intro k hk
    exact coeff_one_add_congr_of_le k
      (fun q hq => h₁ q (hq.trans hk))

structure GoodSmallRoot where
  a : ℚ⟦X⟧
  b : ℚ⟦X⟧
  c : ℚ⟦X⟧
  eqA : a = X * ((1 + a) ^ 2 * (1 + c))
  eqB : b = X * ((1 + b) ^ 2 * (1 + a))
  eqC : c = X * ((1 + c) ^ 2 * (1 + b))

theorem GoodSmallRoot.coeff_eq (left right : GoodSmallRoot) :
    ∀ degree,
      coeff ℚ degree left.a = coeff ℚ degree right.a ∧
      coeff ℚ degree left.b = coeff ℚ degree right.b ∧
      coeff ℚ degree left.c = coeff ℚ degree right.c := by
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree ih =>
      cases degree with
      | zero =>
          have ha := congrArg (coeff ℚ 0) left.eqA
          have ha' := congrArg (coeff ℚ 0) right.eqA
          have hb := congrArg (coeff ℚ 0) left.eqB
          have hb' := congrArg (coeff ℚ 0) right.eqB
          have hc := congrArg (coeff ℚ 0) left.eqC
          have hc' := congrArg (coeff ℚ 0) right.eqC
          simp only [coeff_zero_eq_constantCoeff_apply, map_mul,
            constantCoeff_X, zero_mul] at ha ha' hb hb' hc hc'
          exact ⟨by simpa only [coeff_zero_eq_constantCoeff_apply] using
              ha.trans ha'.symm,
            by simpa only [coeff_zero_eq_constantCoeff_apply] using
              hb.trans hb'.symm,
            by simpa only [coeff_zero_eq_constantCoeff_apply] using
              hc.trans hc'.symm⟩
      | succ degree =>
          have ha : coeff ℚ (degree + 1) left.a =
              coeff ℚ degree ((1 + left.a) ^ 2 * (1 + left.c)) := by
            calc
              _ = coeff ℚ (degree + 1)
                  (X * ((1 + left.a) ^ 2 * (1 + left.c))) :=
                congrArg _ left.eqA
              _ = _ := by
                rw [← pow_one (X : ℚ⟦X⟧)]
                simpa [Nat.add_comm] using coeff_X_pow_mul
                  ((1 + left.a) ^ 2 * (1 + left.c)) 1 degree
          have ha' : coeff ℚ (degree + 1) right.a =
              coeff ℚ degree ((1 + right.a) ^ 2 * (1 + right.c)) := by
            calc
              _ = coeff ℚ (degree + 1)
                  (X * ((1 + right.a) ^ 2 * (1 + right.c))) :=
                congrArg _ right.eqA
              _ = _ := by
                rw [← pow_one (X : ℚ⟦X⟧)]
                simpa [Nat.add_comm] using coeff_X_pow_mul
                  ((1 + right.a) ^ 2 * (1 + right.c)) 1 degree
          have hb : coeff ℚ (degree + 1) left.b =
              coeff ℚ degree ((1 + left.b) ^ 2 * (1 + left.a)) := by
            calc
              _ = coeff ℚ (degree + 1)
                  (X * ((1 + left.b) ^ 2 * (1 + left.a))) :=
                congrArg _ left.eqB
              _ = _ := by
                rw [← pow_one (X : ℚ⟦X⟧)]
                simpa [Nat.add_comm] using coeff_X_pow_mul
                  ((1 + left.b) ^ 2 * (1 + left.a)) 1 degree
          have hb' : coeff ℚ (degree + 1) right.b =
              coeff ℚ degree ((1 + right.b) ^ 2 * (1 + right.a)) := by
            calc
              _ = coeff ℚ (degree + 1)
                  (X * ((1 + right.b) ^ 2 * (1 + right.a))) :=
                congrArg _ right.eqB
              _ = _ := by
                rw [← pow_one (X : ℚ⟦X⟧)]
                simpa [Nat.add_comm] using coeff_X_pow_mul
                  ((1 + right.b) ^ 2 * (1 + right.a)) 1 degree
          have hc : coeff ℚ (degree + 1) left.c =
              coeff ℚ degree ((1 + left.c) ^ 2 * (1 + left.b)) := by
            calc
              _ = coeff ℚ (degree + 1)
                  (X * ((1 + left.c) ^ 2 * (1 + left.b))) :=
                congrArg _ left.eqC
              _ = _ := by
                rw [← pow_one (X : ℚ⟦X⟧)]
                simpa [Nat.add_comm] using coeff_X_pow_mul
                  ((1 + left.c) ^ 2 * (1 + left.b)) 1 degree
          have hc' : coeff ℚ (degree + 1) right.c =
              coeff ℚ degree ((1 + right.c) ^ 2 * (1 + right.b)) := by
            calc
              _ = coeff ℚ (degree + 1)
                  (X * ((1 + right.c) ^ 2 * (1 + right.b))) :=
                congrArg _ right.eqC
              _ = _ := by
                rw [← pow_one (X : ℚ⟦X⟧)]
                simpa [Nat.add_comm] using coeff_X_pow_mul
                  ((1 + right.c) ^ 2 * (1 + right.b)) 1 degree
          have hA := coeff_goodPhi_congr_of_le degree
            (fun k hk => (ih k (by omega)).1)
            (fun k hk => (ih k (by omega)).2.2)
          have hB := coeff_goodPhi_congr_of_le degree
            (fun k hk => (ih k (by omega)).2.1)
            (fun k hk => (ih k (by omega)).1)
          have hC := coeff_goodPhi_congr_of_le degree
            (fun k hk => (ih k (by omega)).2.2)
            (fun k hk => (ih k (by omega)).2.1)
          exact ⟨ha.trans (hA.trans ha'.symm),
            hb.trans (hB.trans hb'.symm),
            hc.trans (hC.trans hc'.symm)⟩

theorem GoodSmallRoot.ext (left right : GoodSmallRoot) : left = right := by
  have hcoeff := GoodSmallRoot.coeff_eq left right
  have ha : left.a = right.a := PowerSeries.ext fun n => (hcoeff n).1
  have hb : left.b = right.b := PowerSeries.ext fun n => (hcoeff n).2.1
  have hc : left.c = right.c := PowerSeries.ext fun n => (hcoeff n).2.2
  rcases left with ⟨leftA, leftB, leftC, leftEqA, leftEqB, leftEqC⟩
  rcases right with ⟨rightA, rightB, rightC, rightEqA, rightEqB, rightEqC⟩
  dsimp only at ha hb hc
  subst rightA
  subst rightB
  subst rightC
  rfl

def GoodSmallRoot.rotate (root : GoodSmallRoot) : GoodSmallRoot where
  a := root.b
  b := root.c
  c := root.a
  eqA := root.eqB
  eqB := root.eqC
  eqC := root.eqA

theorem GoodSmallRoot.cyclic (root : GoodSmallRoot) :
    root.a = root.b ∧ root.b = root.c := by
  have h := congrArg (fun datum : GoodSmallRoot =>
    (datum.a, datum.b, datum.c)) (GoodSmallRoot.ext root root.rotate)
  have h' : root.a = root.b ∧ root.b = root.c ∧ root.c = root.a := by
    simpa [GoodSmallRoot.rotate] using h
  exact ⟨h'.1, h'.2.1⟩

end BenzelProblem6Kernel
