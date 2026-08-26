import FiniteDefects.D4CountingFintypes

/-! # The three ballot sums attached to the five defect classes -/

namespace FiniteDefects

def d4R (x y : ℕ) : ℕ := ballotNumber (x + 2 * y) y

def d4AWeight {n : ℕ} (p : SimplexPoint n) : ℕ :=
  d4R p.u p.v * d4R p.v p.w * d4R p.w p.u

def d4CWeight {n : ℕ} (p : SimplexPoint n) : ℕ :=
  d4R (p.u + 1) p.v * d4R (p.v + 1) p.w * d4R (p.w + 1) p.u

def d4HWeight {n : ℕ} (p : SimplexPoint n) : ℕ :=
  d4R p.u p.v * d4R (p.v + 1) p.w * d4R (p.w + 1) p.u

def d4BoneBWeight {n : ℕ} (p : SimplexPoint n) : ℕ :=
  d4R (p.u + 1) p.v * d4R (p.v + 1) p.w * d4R p.w p.u

def d4BoneCWeight {n : ℕ} (p : SimplexPoint n) : ℕ :=
  d4R (p.u + 1) p.v * d4R p.v p.w * d4R (p.w + 1) p.u

noncomputable def d4A (m : ℕ) : ℕ := ∑ p : SimplexPoint (m + 1), d4AWeight p

noncomputable def d4C (m : ℕ) : ℕ := ∑ p : SimplexPoint m, d4CWeight p

noncomputable def d4H (m : ℕ) : ℕ := ∑ p : SimplexPoint m, d4HWeight p

def simplexRotate (n : ℕ) : SimplexPoint n ≃ SimplexPoint n where
  toFun := fun p =>
    { u := p.w, v := p.u, w := p.v
      sum_eq := by have h := p.sum_eq; omega }
  invFun := fun p =>
    { u := p.v, v := p.w, w := p.u
      sum_eq := by have h := p.sum_eq; omega }
  left_inv := by intro p; apply simplexPoint_ext <;> rfl
  right_inv := by intro p; apply simplexPoint_ext <;> rfl

theorem sum_d4BoneBWeight (m : ℕ) :
    (∑ p : SimplexPoint m, d4BoneBWeight p) = d4H m := by
  unfold d4H
  apply Fintype.sum_equiv (simplexRotate m)
  intro p
  simp [simplexRotate, d4BoneBWeight, d4HWeight,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem sum_d4BoneCWeight (m : ℕ) :
    (∑ p : SimplexPoint m, d4BoneCWeight p) = d4H m := by
  unfold d4H
  apply Fintype.sum_equiv (simplexRotate m).symm
  intro p
  simp [simplexRotate, d4BoneCWeight, d4HWeight,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

noncomputable def d4DefectWeight {m : ℕ} (defect : D4DefectPlacement m) : ℕ :=
  d4R (defect.core .zero).u (defect.core .zero).v *
    d4R (defect.core .one).v (defect.core .one).w *
    d4R (defect.core .two).w (defect.core .two).u

noncomputable def d4DefectParameterWeight {m : ℕ} (parameter : D4DefectParameter m) : ℕ :=
  d4DefectWeight parameter.defect

@[simp] theorem d4DefectParameterWeight_stone1 {m : ℕ}
    (p : SimplexPoint m) :
    d4DefectParameterWeight (.stone1 p) = d4CWeight p := by
  simp [d4DefectParameterWeight, d4DefectWeight,
    D4DefectParameter.defect_core, D4DefectParameter.core,
    d4CWeight]

@[simp] theorem d4DefectParameterWeight_stone2 {m : ℕ}
    (p : SimplexPoint (m + 1)) :
    d4DefectParameterWeight (.stone2 p) = d4AWeight p := by
  simp [d4DefectParameterWeight, d4DefectWeight,
    D4DefectParameter.defect_core, D4DefectParameter.core,
    d4AWeight]

@[simp] theorem d4DefectParameterWeight_boneA {m : ℕ}
    (p : SimplexPoint m) :
    d4DefectParameterWeight (.boneA p) = d4HWeight p := by
  simp [d4DefectParameterWeight, d4DefectWeight,
    D4DefectParameter.defect_core, D4DefectParameter.core,
    d4HWeight]

@[simp] theorem d4DefectParameterWeight_boneB {m : ℕ}
    (p : SimplexPoint m) :
    d4DefectParameterWeight (.boneB p) = d4BoneBWeight p := by
  simp [d4DefectParameterWeight, d4DefectWeight,
    D4DefectParameter.defect_core, D4DefectParameter.core,
    d4BoneBWeight]

@[simp] theorem d4DefectParameterWeight_boneC {m : ℕ}
    (p : SimplexPoint m) :
    d4DefectParameterWeight (.boneC p) = d4BoneCWeight p := by
  simp [d4DefectParameterWeight, d4DefectWeight,
    D4DefectParameter.defect_core, D4DefectParameter.core,
    d4BoneCWeight]

end FiniteDefects
