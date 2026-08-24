import BenzelProblem6Kernel.WZBoundaryMatching
import Mathlib.Data.Fintype.BigOperators

/-!
# Simplex edge and layer equivalences for finite WZ telescoping
-/

namespace BenzelProblem6Kernel

abbrev PositiveUPoint (m : ℕ) := {p : SimplexPoint m // 0 < p.u}
abbrev PositiveVPoint (m : ℕ) := {p : SimplexPoint m // 0 < p.v}
abbrev PositiveWPoint (m : ℕ) := {p : SimplexPoint m // 0 < p.w}
abbrev ZeroWPoint (m : ℕ) := {p : SimplexPoint m // p.w = 0}
abbrev ZeroWPositiveUPoint (m : ℕ) :=
  {p : SimplexPoint m // p.w = 0 ∧ 0 < p.u}
abbrev ZeroWPositiveVPoint (m : ℕ) :=
  {p : SimplexPoint m // p.w = 0 ∧ 0 < p.v}

def notPositiveWEquivZeroW (m : ℕ) :
    {p : SimplexPoint m // ¬0 < p.w} ≃ ZeroWPoint m where
  toFun p := ⟨p.1, by omega⟩
  invFun p := ⟨p.1, by omega⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def nestedZeroWPositiveUEquiv (m : ℕ) :
    {p : ZeroWPoint m // 0 < p.1.u} ≃ ZeroWPositiveUPoint m where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def nestedZeroWPositiveVEquiv (m : ℕ) :
    {p : ZeroWPoint m // 0 < p.1.v} ≃ ZeroWPositiveVPoint m where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def shiftWToUEquiv (m : ℕ) : PositiveWPoint m ≃ PositiveUPoint m where
  toFun p :=
    ⟨{ u := p.1.u + 1
       v := p.1.v
       w := p.1.w - 1
       sum_eq := by have := p.1.sum_eq; omega }, by simp⟩
  invFun p :=
    ⟨{ u := p.1.u - 1
       v := p.1.v
       w := p.1.w + 1
       sum_eq := by have := p.1.sum_eq; omega }, by simp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega
  right_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega

def shiftWToVEquiv (m : ℕ) : PositiveWPoint m ≃ PositiveVPoint m where
  toFun p :=
    ⟨{ u := p.1.u
       v := p.1.v + 1
       w := p.1.w - 1
       sum_eq := by have := p.1.sum_eq; omega }, by simp⟩
  invFun p :=
    ⟨{ u := p.1.u
       v := p.1.v - 1
       w := p.1.w + 1
       sum_eq := by have := p.1.sum_eq; omega }, by simp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega
  right_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega

def liftWEquiv (m : ℕ) : SimplexPoint m ≃ PositiveWPoint (m + 1) where
  toFun p :=
    ⟨{ u := p.u
       v := p.v
       w := p.w + 1
       sum_eq := by have := p.sum_eq; omega }, by simp⟩
  invFun p :=
    { u := p.1.u
      v := p.1.v
      w := p.1.w - 1
      sum_eq := by have := p.1.sum_eq; omega }
  left_inv := by
    intro p
    apply simplexPoint_ext <;> simp
  right_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega

def boundaryShiftUEquiv (m : ℕ) :
    ZeroWPoint m ≃ ZeroWPositiveUPoint (m + 1) where
  toFun p :=
    ⟨{ u := p.1.u + 1
       v := p.1.v
       w := 0
       sum_eq := by have := p.1.sum_eq; omega }, by simp⟩
  invFun p :=
    ⟨{ u := p.1.u - 1
       v := p.1.v
       w := 0
       sum_eq := by have := p.1.sum_eq; omega }, rfl⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega
  right_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega

def boundaryShiftVEquiv (m : ℕ) :
    ZeroWPoint m ≃ ZeroWPositiveVPoint (m + 1) where
  toFun p :=
    ⟨{ u := p.1.u
       v := p.1.v + 1
       w := 0
       sum_eq := by have := p.1.sum_eq; omega }, by simp⟩
  invFun p :=
    ⟨{ u := p.1.u
       v := p.1.v - 1
       w := 0
       sum_eq := by have := p.1.sum_eq; omega }, rfl⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega
  right_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    all_goals simp
    all_goals omega

theorem sum_eq_subtype_of_zero {α : Type*} [Fintype α]
    (predicate : α → Prop) [DecidablePred predicate]
    (f : α → ℚ) (hzero : ∀ a, ¬predicate a → f a = 0) :
    ∑ a : α, f a = ∑ a : {a // predicate a}, f a := by
  classical
  calc
    (∑ a : α, f a) =
        ∑ a : α, if predicate a then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : predicate a
      · simp [ha]
      · simp [ha, hzero a ha]
    _ = ∑ a ∈ Finset.univ.filter predicate, f a := by
      rw [Finset.sum_filter]
    _ = ∑ a : {a // predicate a}, f a := by
      apply Finset.sum_subtype
      intro a
      simp

end BenzelProblem6Kernel
