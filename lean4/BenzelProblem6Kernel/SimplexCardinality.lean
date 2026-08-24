import BenzelProblem6Kernel.OwnerRegionEnergy
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Sum

/-!
# Cardinality of the three-coordinate owner simplex
-/

namespace BenzelProblem6Kernel

theorem simplexPoint_ext {t : ℕ} {p q : SimplexPoint t}
    (hu : p.u = q.u) (hv : p.v = q.v) (hw : p.w = q.w) : p = q := by
  cases p
  cases q
  simp_all

def simplexSuccEquiv (t : ℕ) :
    SimplexPoint (t + 1) ≃ (SimplexPoint t ⊕ Fin (t + 2)) where
  toFun p :=
    if hu : p.u = 0 then
      Sum.inr ⟨p.v, by have := p.sum_eq; omega⟩
    else
      Sum.inl
        { u := p.u - 1
          v := p.v
          w := p.w
          sum_eq := by have := p.sum_eq; omega }
  invFun s :=
    match s with
    | Sum.inl p =>
        { u := p.u + 1
          v := p.v
          w := p.w
          sum_eq := by have := p.sum_eq; omega }
    | Sum.inr v =>
        { u := 0
          v := v
          w := t + 1 - v
          sum_eq := by omega }
  left_inv := by
    intro p
    simp only
    split_ifs with hu
    · apply simplexPoint_ext
      · exact hu.symm
      · simp
      · have hsum := p.sum_eq
        simp
        omega
    · apply simplexPoint_ext
      · have hpos : 0 < p.u := Nat.pos_of_ne_zero hu
        simp
        omega
      · rfl
      · rfl
  right_inv := by
    intro s
    rcases s with p | v
    · simp
    · simp

theorem card_simplexPoint (t : ℕ) :
    Fintype.card (SimplexPoint t) = (t + 2).choose 2 := by
  induction t with
  | zero =>
      have hunique (p : SimplexPoint 0) : p = sourceZero 0 := by
        apply simplexPoint_ext <;>
          simp [sourceZero] <;>
          have := p.sum_eq <;>
          omega
      letI : Unique (SimplexPoint 0) := ⟨⟨sourceZero 0⟩, hunique⟩
      norm_num
  | succ t ih =>
      rw [Fintype.card_congr (simplexSuccEquiv t)]
      rw [Fintype.card_sum, Fintype.card_fin, ih]
      rw [show t + 1 + 2 = (t + 2) + 1 by omega]
      nth_rewrite 2 [Nat.choose_succ_succ]
      simp
      omega

end BenzelProblem6Kernel
