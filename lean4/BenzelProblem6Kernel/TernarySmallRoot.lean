import BenzelProblem6Kernel.SmallRootUniqueness

/-!
# Construction of the ternary small root
-/

namespace BenzelProblem6Kernel

open PowerSeries

noncomputable def ternaryStep (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  X * (1 + series) ^ 3

noncomputable def ternaryIterate : ℕ → ℚ⟦X⟧
  | 0 => 0
  | n + 1 => ternaryStep (ternaryIterate n)

theorem coeff_ternaryStep_zero (series : ℚ⟦X⟧) :
    coeff ℚ 0 (ternaryStep series) = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, ternaryStep, map_mul,
    constantCoeff_X, zero_mul]

theorem ternaryIterate_constantCoeff (iteration : ℕ) :
    constantCoeff ℚ (ternaryIterate iteration) = 0 := by
  cases iteration with
  | zero => simp [ternaryIterate]
  | succ iteration =>
      rw [ternaryIterate, ← coeff_zero_eq_constantCoeff_apply,
        coeff_ternaryStep_zero]

theorem coeff_ternaryStep_succ (series : ℚ⟦X⟧) (degree : ℕ) :
    coeff ℚ (degree + 1) (ternaryStep series) =
      coeff ℚ degree ((1 + series) ^ 3) := by
  rw [ternaryStep, ← pow_one (X : ℚ⟦X⟧)]
  simpa [Nat.add_comm] using coeff_X_pow_mul ((1 + series) ^ 3) 1 degree

theorem coeff_cube_congr_of_le {left right : ℚ⟦X⟧} (degree : ℕ)
    (h : ∀ k ≤ degree, coeff ℚ k left = coeff ℚ k right) :
    coeff ℚ degree ((1 + left) ^ 3) =
      coeff ℚ degree ((1 + right) ^ 3) := by
  rw [show (1 + left) ^ 3 = (1 + left) ^ 2 * (1 + left) by ring,
    show (1 + right) ^ 3 = (1 + right) ^ 2 * (1 + right) by ring]
  exact coeff_goodPhi_congr_of_le degree h h

theorem ternaryIterate_step_stable : ∀ iteration degree,
    degree < iteration →
      coeff ℚ degree (ternaryIterate (iteration + 1)) =
        coeff ℚ degree (ternaryIterate iteration) := by
  intro iteration
  induction iteration using Nat.strong_induction_on with
  | h iteration ih =>
      intro degree hdegree
      cases degree with
      | zero =>
          rw [coeff_zero_eq_constantCoeff_apply,
            coeff_zero_eq_constantCoeff_apply]
          exact (ternaryIterate_constantCoeff _).trans
            (ternaryIterate_constantCoeff _).symm
      | succ degree =>
          have hdegree' : degree < iteration - 0 := by omega
          cases iteration with
          | zero => omega
          | succ previous =>
              simp only [ternaryIterate]
              rw [coeff_ternaryStep_succ, coeff_ternaryStep_succ]
              apply coeff_cube_congr_of_le degree
              intro k hk
              exact ih previous (by omega) k (by omega)

theorem ternaryIterate_coeff_stable_from (degree extra : ℕ) :
    coeff ℚ degree (ternaryIterate (degree + 1 + extra)) =
      coeff ℚ degree (ternaryIterate (degree + 1)) := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      calc
        coeff ℚ degree (ternaryIterate (degree + 1 + (extra + 1))) =
            coeff ℚ degree (ternaryIterate (degree + 1 + extra)) := by
          have hstep := ternaryIterate_step_stable
            (degree + 1 + extra) degree (by omega)
          simpa [Nat.add_assoc] using hstep
        _ = _ := ih

noncomputable def ternarySmallRoot : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    coeff ℚ degree (ternaryIterate (degree + 1))

@[simp] theorem coeff_ternarySmallRoot (degree : ℕ) :
    coeff ℚ degree ternarySmallRoot =
      coeff ℚ degree (ternaryIterate (degree + 1)) := by
  simp [ternarySmallRoot]

theorem ternarySmallRoot_coeff_eq_iterate (degree iteration : ℕ)
    (hiteration : degree + 1 ≤ iteration) :
    coeff ℚ degree ternarySmallRoot =
      coeff ℚ degree (ternaryIterate iteration) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hiteration
  rw [coeff_ternarySmallRoot]
  exact (ternaryIterate_coeff_stable_from degree extra).symm

theorem ternarySmallRoot_equation :
    ternarySmallRoot = ternaryStep ternarySmallRoot := by
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero =>
      simp [coeff_ternarySmallRoot, ternaryIterate,
        coeff_ternaryStep_zero]
  | succ degree =>
      rw [coeff_ternarySmallRoot, ternaryIterate,
        coeff_ternaryStep_succ, coeff_ternaryStep_succ]
      apply coeff_cube_congr_of_le degree
      intro k hk
      exact (ternarySmallRoot_coeff_eq_iterate k (degree + 1)
        (by omega)).symm

theorem ternarySmallRoot_constantCoeff :
    constantCoeff ℚ ternarySmallRoot = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ternarySmallRoot]
  simp [ternaryIterate, coeff_ternaryStep_zero]

noncomputable def goodSmallRoot : GoodSmallRoot where
  a := ternarySmallRoot
  b := ternarySmallRoot
  c := ternarySmallRoot
  eqA := by
    calc
      ternarySmallRoot = X * (1 + ternarySmallRoot) ^ 3 :=
        by simpa [ternaryStep] using ternarySmallRoot_equation
      _ = X * ((1 + ternarySmallRoot) ^ 2 *
          (1 + ternarySmallRoot)) := by ring
  eqB := by
    calc
      ternarySmallRoot = X * (1 + ternarySmallRoot) ^ 3 :=
        by simpa [ternaryStep] using ternarySmallRoot_equation
      _ = X * ((1 + ternarySmallRoot) ^ 2 *
          (1 + ternarySmallRoot)) := by ring
  eqC := by
    calc
      ternarySmallRoot = X * (1 + ternarySmallRoot) ^ 3 :=
        by simpa [ternaryStep] using ternarySmallRoot_equation
      _ = X * ((1 + ternarySmallRoot) ^ 2 *
          (1 + ternarySmallRoot)) := by ring

theorem goodSmallRoot_unique (root : GoodSmallRoot) : root = goodSmallRoot :=
  GoodSmallRoot.ext root goodSmallRoot

end BenzelProblem6Kernel
