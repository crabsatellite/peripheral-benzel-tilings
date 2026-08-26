import D4KernelOnly.GeneralClassZeroSideFive
import D4KernelOnly.GeneralTilingBoundaryCancellation

/-! # Exact side-five boundary cells of a class-zero benzel -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def czSpurCell (s r : ℕ) : Cell := (-((r : ℤ)), (s : ℤ) + r)

def CZPositiveBoundary (s r : ℕ) (cell : Cell) : Prop :=
  (∃ q : ℤ, 0 ≤ q ∧ q < (r : ℤ) - 1 ∧
    cell = (r - 2 * q - 2, s + q + 1)) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < r ∧
    cell = (s + q, q - s - r + 1)) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < s ∧
    (cell = (s + r - q - 1, -s + 2 * q + 1) ∨
      cell = (s + r - q - 1, -s + 2 * q + 2)))

theorem czPositiveBoundary_iff_region
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    CZPositiveBoundary s r cell ↔
      inBenzel (2 * s + r) (s + 2 * r) cell ∧
        ¬inBenzel (2 * s + r) (s + 2 * r)
          (neighboringCell cell .side₅) := by
  rcases cell with ⟨i, j⟩
  constructor
  · rintro (⟨q, hq0, hqr, heq⟩ |
      ⟨q, hq0, hqr, heq⟩ | ⟨q, hq0, hqs, heq | heq⟩)
    all_goals simp only [Prod.mk.injEq] at heq
    all_goals rcases heq with ⟨rfl, rfl⟩
    all_goals simp only [inBenzel, neighboringCell]
    all_goals push_cast
    all_goals omega
  · intro h
    simp only [inBenzel, neighboringCell] at h
    push_cast at h
    by_cases hfirst : j - i = 1 - 2 * (s : ℤ) - r
    · right; left
      refine ⟨i - s, by omega, by omega, ?_⟩
      apply Prod.ext <;> omega
    · by_cases hm1 : 2 * i + j - 1 = (s : ℤ) + 2 * r - 1
      · right; right
        refine ⟨(s : ℤ) + r - i - 1, by omega, by omega, Or.inr ?_⟩
        apply Prod.ext <;> omega
      · by_cases hm2 : 2 * i + j - 1 = (s : ℤ) + 2 * r - 2
        · right; right
          refine ⟨(s : ℤ) + r - i - 1, by omega, by omega, Or.inl ?_⟩
          apply Prod.ext <;> omega
        · left
          have hthird : 1 - i - 2 * j = 1 - 2 * (s : ℤ) - r := by omega
          refine ⟨j - s - 1, by omega, by omega, ?_⟩
          apply Prod.ext <;> omega

def CZNegativeBoundary (s r : ℕ) (cell : Cell) : Prop :=
  (∃ q : ℤ, 0 ≤ q ∧ q < (s : ℤ) - 1 ∧
    cell = (-r - q - 1, s + r - q - 1)) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < r ∧
    (cell = (-s - r + q, r - 2 * q) ∨
      cell = (-s - r + q + 1, r - 2 * q - 1))) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < s ∧
    cell = (-s + 1 + 2 * q, -r - q))

theorem czNegativeBoundary_iff_region
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    CZNegativeBoundary s r cell ↔
      ¬inBenzel (2 * s + r) (s + 2 * r) cell ∧
        inBenzel (2 * s + r) (s + 2 * r)
          (neighboringCell cell .side₅) := by
  rcases cell with ⟨i, j⟩
  constructor
  · rintro (⟨q, hq0, hqs, heq⟩ |
      ⟨q, hq0, hqr, heq | heq⟩ | ⟨q, hq0, hqs, heq⟩)
    all_goals simp only [Prod.mk.injEq] at heq
    all_goals rcases heq with ⟨rfl, rfl⟩
    all_goals simp only [inBenzel, neighboringCell]
    all_goals push_cast
    all_goals omega
  · intro h
    simp only [inBenzel, neighboringCell] at h
    push_cast at h
    by_cases hmiddle : 1 - i - 2 * j = (s : ℤ) + 2 * r
    · right; right
      refine ⟨-r - j, by omega, by omega, ?_⟩
      apply Prod.ext <;> omega
    · by_cases hl0 : 2 * i + j - 1 = -2 * (s : ℤ) - r
      · right; left
        refine ⟨i + s + r - 1, by omega, by omega, Or.inr ?_⟩
        apply Prod.ext <;> omega
      · by_cases hl1 : 2 * i + j - 1 = -2 * (s : ℤ) - r - 1
        · right; left
          refine ⟨i + s + r, by omega, by omega, Or.inl ?_⟩
          apply Prod.ext <;> omega
        · left
          have hlast : j - i = (s : ℤ) + 2 * r := by omega
          refine ⟨-r - i - 1, by omega, by omega, ?_⟩
          apply Prod.ext <;> omega

def czPositiveFamily0 (s r : ℕ) : List Cell :=
  (List.range (r - 1)).map fun q : ℕ =>
    ((r : ℤ) - 2 * q - 2, (s : ℤ) + q + 1)

def czPositiveFamily1 (s r : ℕ) : List Cell :=
  (List.range r).map fun q : ℕ =>
    ((s : ℤ) + q, (q : ℤ) - s - r + 1)

def czPositiveFamily2 (s r : ℕ) : List Cell :=
  (List.range s).flatMap fun q : ℕ =>
    [((s : ℤ) + r - q - 1, -(s : ℤ) + 2 * q + 1),
      ((s : ℤ) + r - q - 1, -(s : ℤ) + 2 * q + 2)]

def czSideFiveCells (s r : ℕ) : List Cell :=
  czPositiveFamily0 s r ++ (czPositiveFamily1 s r ++ czPositiveFamily2 s r)

def czNegativeFamily0 (s r : ℕ) : List Cell :=
  (List.range (s - 1)).map fun q : ℕ =>
    (-((r : ℤ)) - q - 1, (s : ℤ) + r - q - 1)

def czNegativeFamily1 (s r : ℕ) : List Cell :=
  (List.range r).flatMap fun q : ℕ =>
    [(-((s : ℤ)) - r + q, (r : ℤ) - 2 * q),
      (-((s : ℤ)) - r + q + 1, (r : ℤ) - 2 * q - 1)]

def czNegativeFamily2 (s r : ℕ) : List Cell :=
  (List.range s).map fun q : ℕ =>
    (-((s : ℤ)) + 1 + 2 * q, -((r : ℤ)) - q)

def czSideFiveNegativeCells (s r : ℕ) : List Cell :=
  czNegativeFamily0 s r ++ (czNegativeFamily1 s r ++ czNegativeFamily2 s r)

theorem mem_czSideFiveCells_iff_predicate
    (s r : ℕ) (hr : 1 ≤ r) (cell : Cell) :
    cell ∈ czSideFiveCells s r ↔ CZPositiveBoundary s r cell := by
  simp [czSideFiveCells, czPositiveFamily0, czPositiveFamily1,
    czPositiveFamily2, CZPositiveBoundary, List.mem_flatMap]
  constructor
  · rintro (⟨q, hq, heq⟩ | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩)
    · exact Or.inl ⟨q, by omega, by
        have hcast : (q : ℤ) < ((r - 1 : ℕ) : ℤ) := by exact_mod_cast hq
        push_cast [Nat.cast_sub hr] at hcast
        exact hcast, heq.symm⟩
    · exact Or.inr (Or.inl ⟨q, by omega, by exact_mod_cast hq, heq.symm⟩)
    · exact Or.inr (Or.inr ⟨q, by omega, by exact_mod_cast hq, by simpa [eq_comm] using heq⟩)
  · rintro (⟨q, hq0, hqr, heq⟩ | ⟨q, hq0, hqr, heq⟩ |
      ⟨q, hq0, hqs, heq⟩)
    all_goals let n := q.toNat
    all_goals have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
    · left
      refine ⟨n, ?_, ?_⟩
      · have hnlt : (n : ℤ) < (r : ℤ) - 1 := by simpa [hn] using hqr
        exact_mod_cast hnlt
      · simpa [hn] using heq.symm
    · right; left
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (show (n : ℤ) < r by simpa [hn] using hqr)
      · simpa [hn] using heq.symm
    · right; right
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (show (n : ℤ) < s by simpa [hn] using hqs)
      · simpa [hn, eq_comm] using heq

theorem mem_czSideFiveNegativeCells_iff_predicate
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    cell ∈ czSideFiveNegativeCells s r ↔ CZNegativeBoundary s r cell := by
  simp [czSideFiveNegativeCells, czNegativeFamily0, czNegativeFamily1,
    czNegativeFamily2, CZNegativeBoundary, List.mem_flatMap]
  constructor
  · rintro (⟨q, hq, heq⟩ | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩)
    · exact Or.inl ⟨q, by omega, by
        have hcast : (q : ℤ) < ((s - 1 : ℕ) : ℤ) := by exact_mod_cast hq
        push_cast [Nat.cast_sub hs] at hcast
        exact hcast, heq.symm⟩
    · exact Or.inr (Or.inl ⟨q, by omega, by exact_mod_cast hq,
        by simpa [eq_comm] using heq⟩)
    · exact Or.inr (Or.inr ⟨q, by omega, by exact_mod_cast hq, heq.symm⟩)
  · rintro (⟨q, hq0, hqs, heq⟩ | ⟨q, hq0, hqr, heq⟩ |
      ⟨q, hq0, hqs, heq⟩)
    all_goals let n := q.toNat
    all_goals have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
    · left
      refine ⟨n, ?_, ?_⟩
      · have hnlt : (n : ℤ) < (s : ℤ) - 1 := by simpa [hn] using hqs
        exact_mod_cast hnlt
      · simpa [hn] using heq.symm
    · right; left
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (show (n : ℤ) < r by simpa [hn] using hqr)
      · simpa [hn, eq_comm] using heq
    · right; right
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (show (n : ℤ) < s by simpa [hn] using hqs)
      · simpa [hn] using heq.symm

theorem mem_czSideFiveCells_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    cell ∈ czSideFiveCells s r ↔
      inBenzel (2 * s + r) (s + 2 * r) cell ∧
        ¬inBenzel (2 * s + r) (s + 2 * r)
          (neighboringCell cell .side₅) :=
  (mem_czSideFiveCells_iff_predicate s r hr cell).trans
    (czPositiveBoundary_iff_region s r hs hr cell)

theorem mem_czSideFiveNegativeCells_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (cell : Cell) :
    cell ∈ czSideFiveNegativeCells s r ↔
      ¬inBenzel (2 * s + r) (s + 2 * r) cell ∧
        inBenzel (2 * s + r) (s + 2 * r)
          (neighboringCell cell .side₅) :=
  (mem_czSideFiveNegativeCells_iff_predicate s r hs cell).trans
    (czNegativeBoundary_iff_region s r hs hr cell)

end FiniteDefects
