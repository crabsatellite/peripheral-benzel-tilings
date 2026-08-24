import Mathlib.Tactic.Ring

/-!
# Algebra of shadow words

The Conway--Lagarias shadow path is encoded by its lattice displacement and
the normalized shoelace numerator `sum_{i < j} v_i cross v_j`.  Keeping this
summary as a three-integer object makes concatenation and repeated boundary
blocks exact and inexpensive to elaborate.
-/

namespace BenzelProblem6Kernel

structure ShadowStep where
  x : ℤ
  y : ℤ
  deriving DecidableEq

@[ext] theorem shadowStep_ext (left right : ShadowStep)
    (hx : left.x = right.x) (hy : left.y = right.y) : left = right := by
  cases left
  cases right
  simp_all

def shadowCross (left right : ShadowStep) : ℤ :=
  left.x * right.y - left.y * right.x

def shadowA : ShadowStep := ⟨1, 0⟩
def shadowB : ShadowStep := ⟨0, 1⟩
def shadowC : ShadowStep := ⟨-1, -1⟩

def ShadowStep.neg (step : ShadowStep) : ShadowStep :=
  ⟨-step.x, -step.y⟩

@[simp] theorem ShadowStep.neg_x (step : ShadowStep) : step.neg.x = -step.x := rfl

@[simp] theorem ShadowStep.neg_y (step : ShadowStep) : step.neg.y = -step.y := rfl

@[simp] theorem ShadowStep.neg_neg (step : ShadowStep) : step.neg.neg = step := by
  cases step
  simp [ShadowStep.neg]

structure ShadowSummary where
  x : ℤ
  y : ℤ
  areaNumerator : ℤ
  deriving DecidableEq

@[ext] theorem shadowSummary_ext (left right : ShadowSummary)
    (hx : left.x = right.x) (hy : left.y = right.y)
    (harea : left.areaNumerator = right.areaNumerator) : left = right := by
  cases left
  cases right
  simp_all

def ShadowSummary.displacement (summary : ShadowSummary) : ShadowStep :=
  ⟨summary.x, summary.y⟩

def ShadowSummary.empty : ShadowSummary := ⟨0, 0, 0⟩

def ShadowSummary.single (step : ShadowStep) : ShadowSummary :=
  ⟨step.x, step.y, 0⟩

def ShadowSummary.append (left right : ShadowSummary) : ShadowSummary :=
  ⟨left.x + right.x,
    left.y + right.y,
    left.areaNumerator + right.areaNumerator +
      shadowCross left.displacement right.displacement⟩

@[simp] theorem ShadowSummary.empty_append (summary : ShadowSummary) :
    ShadowSummary.empty.append summary = summary := by
  cases summary
  simp [ShadowSummary.empty, ShadowSummary.append,
    ShadowSummary.displacement, shadowCross]

@[simp] theorem ShadowSummary.append_empty (summary : ShadowSummary) :
    summary.append ShadowSummary.empty = summary := by
  cases summary
  simp [ShadowSummary.empty, ShadowSummary.append,
    ShadowSummary.displacement, shadowCross]

theorem ShadowSummary.append_assoc (first second third : ShadowSummary) :
    (first.append second).append third =
      first.append (second.append third) := by
  cases first
  cases second
  cases third
  apply shadowSummary_ext <;>
    simp only [ShadowSummary.append, ShadowSummary.displacement, shadowCross] <;>
    ring

def shadowWordSummary : List ShadowStep → ShadowSummary
  | [] => ShadowSummary.empty
  | step :: rest =>
      (ShadowSummary.single step).append (shadowWordSummary rest)

@[simp] theorem shadowWordSummary_nil :
    shadowWordSummary [] = ShadowSummary.empty := rfl

theorem shadowWordSummary_append (left right : List ShadowStep) :
    shadowWordSummary (left ++ right) =
      (shadowWordSummary left).append (shadowWordSummary right) := by
  induction left with
  | nil => simp [shadowWordSummary]
  | cons step rest ih =>
      simp only [List.cons_append, shadowWordSummary, ih]
      rw [ShadowSummary.append_assoc]

def shadowWordPower (word : List ShadowStep) : ℕ → List ShadowStep
  | 0 => []
  | exponent + 1 => shadowWordPower word exponent ++ word

@[simp] theorem shadowWordPower_zero (word : List ShadowStep) :
    shadowWordPower word 0 = [] := rfl

@[simp] theorem shadowWordPower_succ (word : List ShadowStep) (exponent : ℕ) :
    shadowWordPower word (exponent + 1) =
      shadowWordPower word exponent ++ word := rfl

def ShadowSummary.scale (exponent : ℕ) (summary : ShadowSummary) :
    ShadowSummary :=
  ⟨(exponent : ℤ) * summary.x,
    (exponent : ℤ) * summary.y,
    (exponent : ℤ) * summary.areaNumerator⟩

theorem shadowCross_self (step : ShadowStep) :
    shadowCross step step = 0 := by
  simp only [shadowCross]
  ring

theorem shadowWordSummary_power (word : List ShadowStep) (exponent : ℕ) :
    shadowWordSummary (shadowWordPower word exponent) =
      ShadowSummary.scale exponent (shadowWordSummary word) := by
  induction exponent with
  | zero => simp [ShadowSummary.scale, ShadowSummary.empty]
  | succ exponent ih =>
      rw [shadowWordPower_succ, shadowWordSummary_append, ih]
      cases hsummary : shadowWordSummary word with
      | mk x y area =>
          simp only [ShadowSummary.scale, ShadowSummary.append,
            ShadowSummary.displacement, shadowCross]
          congr <;> push_cast <;> ring

theorem shadowWordSummary_reverse_neg (word : List ShadowStep) :
    shadowWordSummary (word.reverse.map ShadowStep.neg) =
      ⟨-(shadowWordSummary word).x,
        -(shadowWordSummary word).y,
        -(shadowWordSummary word).areaNumerator⟩ := by
  induction word with
  | nil => simp [shadowWordSummary, ShadowSummary.empty]
  | cons step rest ih =>
      simp only [List.reverse_cons, List.map_append, List.map_singleton,
        shadowWordSummary_append, ih, shadowWordSummary,
        ShadowSummary.single, ShadowSummary.empty, ShadowSummary.append,
        ShadowSummary.displacement, shadowCross, ShadowStep.neg_x,
        ShadowStep.neg_y]
      apply shadowSummary_ext <;> ring

end BenzelProblem6Kernel
