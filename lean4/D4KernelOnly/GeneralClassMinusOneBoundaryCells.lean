import D4KernelOnly.GeneralClassMinusOneSideFive
import D4KernelOnly.GeneralTilingBoundaryCancellation

/-! # Exact inside and outside side-five cells for class-minus-one benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

def cmoSpurCell (s r : ℕ) : Cell := (s, -((r : ℤ)) - s)

def cmoPositiveFamily0 (s r : ℕ) : List Cell :=
  (List.range r).map fun q : ℕ =>
    ((s : ℤ) + q + 1, (q : ℤ) - r - s + 1)

def cmoPositiveFamily1 (s r : ℕ) : List Cell :=
  (List.range s).flatMap fun q : ℕ =>
    [((r : ℤ) + s - q, 2 * (q : ℤ) - s + 1),
      ((r : ℤ) + s - q - 1, 2 * (q : ℤ) - s + 2)]

def cmoPositiveFamily2 (s r : ℕ) : List Cell :=
  (List.range r).map fun q : ℕ =>
    ((r : ℤ) - 2 * q - 1, (s : ℤ) + q + 1)

def cmoSideFiveCells (s r : ℕ) : List Cell :=
  cmoPositiveFamily0 s r ++
    (cmoPositiveFamily1 s r ++ cmoPositiveFamily2 s r)

def CMOPositiveBoundary (s r : ℕ) (cell : Cell) : Prop :=
  (∃ q : ℤ, 0 ≤ q ∧ q < r ∧
    cell = (s + q + 1, q - r - s + 1)) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < s ∧
    (cell = (r + s - q, 2 * q - s + 1) ∨
      cell = (r + s - q - 1, 2 * q - s + 2))) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < r ∧
    cell = (r - 2 * q - 1, s + q + 1))

theorem cmoPositiveBoundary_iff_region
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    CMOPositiveBoundary s r cell ↔
      inBenzel (2 * s + r + 1) (s + 2 * r + 1) cell ∧
        ¬inBenzel (2 * s + r + 1) (s + 2 * r + 1)
          (neighboringCell cell .side₅) := by
  rcases cell with ⟨i, j⟩
  constructor
  · rintro (⟨q, hq0, hqr, heq⟩ |
      ⟨q, hq0, hqs, heq | heq⟩ | ⟨q, hq0, hqr, heq⟩)
    all_goals simp only [Prod.mk.injEq] at heq
    all_goals rcases heq with ⟨rfl, rfl⟩
    all_goals simp only [inBenzel, neighboringCell]
    all_goals push_cast
    all_goals omega
  · intro h
    simp only [inBenzel, neighboringCell] at h
    push_cast at h
    by_cases hfirst : j - i = -2 * (s : ℤ) - r
    · left
      refine ⟨i - s - 1, by omega, by omega, ?_⟩
      apply Prod.ext <;> omega
    · by_cases hthird : 1 - i - 2 * j = -2 * (s : ℤ) - r
      · right; right
        refine ⟨j - s - 1, by omega, by omega, ?_⟩
        apply Prod.ext <;> omega
      · right; left
        have hmid :
            2 * i + j - 1 = (s : ℤ) + 2 * r ∨
              2 * i + j - 1 = (s : ℤ) + 2 * r - 1 := by
          omega
        rcases hmid with hm | hm
        · refine ⟨(r : ℤ) + s - i, by omega, by omega, Or.inl ?_⟩
          apply Prod.ext <;> omega
        · refine ⟨(r : ℤ) + s - i - 1, by omega, by omega, Or.inr ?_⟩
          apply Prod.ext <;> omega

theorem mem_cmoSideFiveCells_iff_predicate
    (s r : ℕ) (cell : Cell) :
    cell ∈ cmoSideFiveCells s r ↔ CMOPositiveBoundary s r cell := by
  have h0 : cell ∈ cmoPositiveFamily0 s r ↔
      ∃ q : ℕ, q < r ∧
        cell = ((s : ℤ) + q + 1, (q : ℤ) - r - s + 1) := by
    simp [cmoPositiveFamily0, eq_comm]
  have h1 : cell ∈ cmoPositiveFamily1 s r ↔
      ∃ q : ℕ, q < s ∧
        (cell = ((r : ℤ) + s - q, 2 * (q : ℤ) - s + 1) ∨
          cell = ((r : ℤ) + s - q - 1, 2 * (q : ℤ) - s + 2)) := by
    simp [cmoPositiveFamily1]
  have h2 : cell ∈ cmoPositiveFamily2 s r ↔
      ∃ q : ℕ, q < r ∧
        cell = ((r : ℤ) - 2 * q - 1, (s : ℤ) + q + 1) := by
    simp [cmoPositiveFamily2, eq_comm]
  rw [cmoSideFiveCells, List.mem_append, List.mem_append]
  constructor
  · intro hmem
    rcases hmem with hmem | hmem
    · rw [h0] at hmem
      obtain ⟨q, hq, heq⟩ := hmem
      exact Or.inl ⟨q, by omega, by exact_mod_cast hq, heq⟩
    · rcases hmem with hmem | hmem
      · rw [h1] at hmem
        obtain ⟨q, hq, heq⟩ := hmem
        exact Or.inr (Or.inl ⟨q, by omega, by exact_mod_cast hq, heq⟩)
      · rw [h2] at hmem
        obtain ⟨q, hq, heq⟩ := hmem
        exact Or.inr (Or.inr ⟨q, by omega, by exact_mod_cast hq, heq⟩)
  · intro hpred
    rcases hpred with hpred | hpred
    · obtain ⟨q, hq0, hqr, heq⟩ := hpred
      let n := q.toNat
      have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
      left
      rw [h0]
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (show (n : ℤ) < r by simpa [hn] using hqr)
      · simpa [hn] using heq
    · rcases hpred with hpred | hpred
      · obtain ⟨q, hq0, hqs, heq⟩ := hpred
        let n := q.toNat
        have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
        right; left
        rw [h1]
        refine ⟨n, ?_, ?_⟩
        · exact_mod_cast (show (n : ℤ) < s by simpa [hn] using hqs)
        · simpa [hn] using heq
      · obtain ⟨q, hq0, hqr, heq⟩ := hpred
        let n := q.toNat
        have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
        right; right
        rw [h2]
        refine ⟨n, ?_, ?_⟩
        · exact_mod_cast (show (n : ℤ) < r by simpa [hn] using hqr)
        · simpa [hn] using heq

theorem mem_cmoSideFiveCells_iff
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    cell ∈ cmoSideFiveCells s r ↔
      inBenzel (2 * s + r + 1) (s + 2 * r + 1) cell ∧
        ¬inBenzel (2 * s + r + 1) (s + 2 * r + 1)
          (neighboringCell cell .side₅) :=
  (mem_cmoSideFiveCells_iff_predicate s r cell).trans
    (cmoPositiveBoundary_iff_region s r hs cell)

def CMONegativeBoundary (s r : ℕ) (cell : Cell) : Prop :=
  (∃ q : ℤ, 0 ≤ q ∧ q < r ∧
    (cell = (-(r : ℤ) - s + q, (r : ℤ) - 2 * q) ∨
      cell = (-(r : ℤ) - s + q, (r : ℤ) - 2 * q - 1))) ∨
  cell = (-(s : ℤ), -(r : ℤ)) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < (s : ℤ) - 1 ∧
    cell = (-(s : ℤ) + 2 + 2 * q, -(r : ℤ) - 1 - q)) ∨
  (∃ q : ℤ, 0 ≤ q ∧ q < s ∧
    cell = (-(r : ℤ) - q - 1, (r : ℤ) + s - q))

theorem cmoNegativeBoundary_iff_region
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    CMONegativeBoundary s r cell ↔
      ¬inBenzel (2 * s + r + 1) (s + 2 * r + 1) cell ∧
        inBenzel (2 * s + r + 1) (s + 2 * r + 1)
          (neighboringCell cell .side₅) := by
  rcases cell with ⟨i, j⟩
  constructor
  · rintro (⟨q, hq0, hqr, heq | heq⟩ | heq |
      ⟨q, hq0, hqs, heq⟩ | ⟨q, hq0, hqs, heq⟩)
    all_goals simp only [Prod.mk.injEq] at heq
    all_goals rcases heq with ⟨rfl, rfl⟩
    all_goals simp only [inBenzel, neighboringCell]
    all_goals push_cast
    all_goals omega
  · intro h
    simp only [inBenzel, neighboringCell] at h
    push_cast at h
    by_cases hlast : j - i = (s : ℤ) + 2 * r + 1
    · right; right; right
      refine ⟨-r - i - 1, by omega, by omega, ?_⟩
      apply Prod.ext <;> omega
    · by_cases hmiddle : 1 - i - 2 * j = (s : ℤ) + 2 * r + 1
      · let q : ℤ := -r - j - 1
        by_cases hq : q = -1
        · right; left
          dsimp [q] at hq
          apply Prod.ext <;> omega
        · right; right; left
          refine ⟨q, by dsimp [q]; omega, by dsimp [q]; omega, ?_⟩
          apply Prod.ext <;> dsimp [q] <;> omega
      · left
        let q : ℤ := i + r + s
        refine ⟨q, by dsimp [q]; omega, by dsimp [q]; omega, ?_⟩
        have hlower :
            2 * i + j - 1 = -2 * (s : ℤ) - r - 1 ∨
              2 * i + j - 1 = -2 * (s : ℤ) - r - 2 := by
          omega
        rcases hlower with hl | hl
        · left; apply Prod.ext <;> dsimp [q] <;> omega
        · right; apply Prod.ext <;> dsimp [q] <;> omega

def cmoNegativeFamily0 (s r : ℕ) : List Cell :=
  (List.range r).flatMap fun q : ℕ =>
    [(-((r : ℤ)) - s + q, (r : ℤ) - 2 * q),
      (-((r : ℤ)) - s + q, (r : ℤ) - 2 * q - 1)]

def cmoNegativeFamily1 (s r : ℕ) : List Cell :=
  [(-((s : ℤ)), -((r : ℤ)))]

def cmoNegativeFamily2 (s r : ℕ) : List Cell :=
  (List.range (s - 1)).map fun q : ℕ =>
    (-((s : ℤ)) + 2 + 2 * q, -((r : ℤ)) - 1 - q)

def cmoNegativeFamily3 (s r : ℕ) : List Cell :=
  (List.range s).map fun q : ℕ =>
    (-((r : ℤ)) - q - 1, (r : ℤ) + s - q)

def cmoSideFiveNegativeCells (s r : ℕ) : List Cell :=
  cmoNegativeFamily0 s r ++
    (cmoNegativeFamily1 s r ++
      (cmoNegativeFamily2 s r ++ cmoNegativeFamily3 s r))

theorem mem_cmoSideFiveNegativeCells_iff_predicate
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    cell ∈ cmoSideFiveNegativeCells s r ↔
      CMONegativeBoundary s r cell := by
  have h0 : cell ∈ cmoNegativeFamily0 s r ↔
      ∃ q : ℕ, q < r ∧
        (cell = (-((r : ℤ)) - s + q, (r : ℤ) - 2 * q) ∨
          cell = (-((r : ℤ)) - s + q, (r : ℤ) - 2 * q - 1)) := by
    simp [cmoNegativeFamily0]
  have h1 : cell ∈ cmoNegativeFamily1 s r ↔
      cell = (-((s : ℤ)), -((r : ℤ))) := by
    simp [cmoNegativeFamily1]
  have h2 : cell ∈ cmoNegativeFamily2 s r ↔
      ∃ q : ℕ, q < s - 1 ∧
        cell = (-((s : ℤ)) + 2 + 2 * q, -((r : ℤ)) - 1 - q) := by
    simp [cmoNegativeFamily2, eq_comm]
  have h3 : cell ∈ cmoNegativeFamily3 s r ↔
      ∃ q : ℕ, q < s ∧
        cell = (-((r : ℤ)) - q - 1, (r : ℤ) + s - q) := by
    simp [cmoNegativeFamily3, eq_comm]
  rw [cmoSideFiveNegativeCells, List.mem_append, List.mem_append,
    List.mem_append]
  constructor
  · intro hmem
    rcases hmem with hmem | hmem
    · rw [h0] at hmem
      obtain ⟨q, hq, heq⟩ := hmem
      exact Or.inl ⟨q, by omega, by exact_mod_cast hq, heq⟩
    · rcases hmem with hmem | hmem
      · rw [h1] at hmem
        exact Or.inr (Or.inl hmem)
      · rcases hmem with hmem | hmem
        · rw [h2] at hmem
          obtain ⟨q, hq, heq⟩ := hmem
          have hqZ : (q : ℤ) < (s : ℤ) - 1 := by
            have hcast : (q : ℤ) < ((s - 1 : ℕ) : ℤ) := by
              exact_mod_cast hq
            push_cast [Nat.cast_sub hs] at hcast
            exact hcast
          exact Or.inr (Or.inr (Or.inl ⟨q, by omega, hqZ, heq⟩))
        · rw [h3] at hmem
          obtain ⟨q, hq, heq⟩ := hmem
          exact Or.inr (Or.inr (Or.inr
            ⟨q, by omega, by exact_mod_cast hq, heq⟩))
  · intro hpred
    rcases hpred with hpred | hpred
    · obtain ⟨q, hq0, hqr, heq⟩ := hpred
      left
      rw [h0]
      let n := q.toNat
      have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (show (n : ℤ) < r by simpa [hn] using hqr)
      · simpa [hn] using heq
    · rcases hpred with hpred | hpred
      · right; left
        rwa [h1]
      · rcases hpred with hpred | hpred
        · obtain ⟨q, hq0, hqs, heq⟩ := hpred
          right; right; left
          rw [h2]
          let n := q.toNat
          have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
          refine ⟨n, ?_, ?_⟩
          · have hnlt : (n : ℤ) < (s : ℤ) - 1 := by simpa [hn] using hqs
            exact_mod_cast hnlt
          · simpa [hn] using heq
        · obtain ⟨q, hq0, hqs, heq⟩ := hpred
          right; right; right
          rw [h3]
          let n := q.toNat
          have hn : (n : ℤ) = q := by simp [n, Int.toNat_of_nonneg hq0]
          refine ⟨n, ?_, ?_⟩
          · exact_mod_cast (show (n : ℤ) < s by simpa [hn] using hqs)
          · simpa [hn] using heq

theorem mem_cmoSideFiveNegativeCells_iff
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    cell ∈ cmoSideFiveNegativeCells s r ↔
      ¬inBenzel (2 * s + r + 1) (s + 2 * r + 1) cell ∧
        inBenzel (2 * s + r + 1) (s + 2 * r + 1)
          (neighboringCell cell .side₅) :=
  (mem_cmoSideFiveNegativeCells_iff_predicate s r hs cell).trans
    (cmoNegativeBoundary_iff_region s r hs cell)

theorem cmoPositiveFamily0_nodup (s r : ℕ) :
    (cmoPositiveFamily0 s r).Nodup := by
  unfold cmoPositiveFamily0
  apply (List.nodup_range r).map
  intro a b hab
  have h := congrArg Prod.fst hab
  simp only [Function.comp_apply] at h
  omega

theorem cmoPositiveFamily1_nodup (s r : ℕ) :
    (cmoPositiveFamily1 s r).Nodup := by
  unfold cmoPositiveFamily1
  rw [List.nodup_flatMap]
  constructor
  · intro q hq
    simp
  · apply (List.pairwise_lt_range s).imp
    intro a b hab
    simp [Function.onFun, List.disjoint_left]
    omega

theorem cmoPositiveFamily2_nodup (s r : ℕ) :
    (cmoPositiveFamily2 s r).Nodup := by
  unfold cmoPositiveFamily2
  apply (List.nodup_range r).map
  intro a b hab
  have h := congrArg Prod.snd hab
  simp only [Function.comp_apply] at h
  omega

theorem cmoPositiveFamily0_disjoint_family1 (s r : ℕ) :
    List.Disjoint (cmoPositiveFamily0 s r) (cmoPositiveFamily1 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h1
  simp [cmoPositiveFamily0, cmoPositiveFamily1] at h0 h1
  rcases h0 with ⟨a, ha, rfl⟩
  rcases h1 with ⟨b, hb, h | h⟩
  · have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    simp at hfst hsnd
    omega
  · have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    simp at hfst hsnd
    omega

theorem cmoPositiveFamily0_disjoint_family2 (s r : ℕ) :
    List.Disjoint (cmoPositiveFamily0 s r) (cmoPositiveFamily2 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h2
  simp [cmoPositiveFamily0, cmoPositiveFamily2] at h0 h2
  rcases h0 with ⟨a, ha, rfl⟩
  rcases h2 with ⟨b, hb, h⟩
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp at hfst hsnd
  omega

theorem cmoPositiveFamily1_disjoint_family2 (s r : ℕ) :
    List.Disjoint (cmoPositiveFamily1 s r) (cmoPositiveFamily2 s r) := by
  rw [List.disjoint_left]
  intro cell h1 h2
  simp [cmoPositiveFamily1, cmoPositiveFamily2] at h1 h2
  rcases h1 with ⟨a, ha, h | h⟩
  · rcases h2 with ⟨b, hb, h2⟩
    have heq := h.symm.trans h2.symm
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    simp at hfst hsnd
    omega
  · rcases h2 with ⟨b, hb, h2⟩
    have heq := h.symm.trans h2.symm
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    simp at hfst hsnd
    omega

theorem cmoSideFiveCells_nodup (s r : ℕ) :
    (cmoSideFiveCells s r).Nodup := by
  rw [cmoSideFiveCells, List.nodup_append]
  constructor
  · exact cmoPositiveFamily0_nodup s r
  constructor
  · rw [List.nodup_append]
    exact ⟨cmoPositiveFamily1_nodup s r,
      cmoPositiveFamily2_nodup s r,
      cmoPositiveFamily1_disjoint_family2 s r⟩
  · rw [List.disjoint_append_right]
    exact ⟨cmoPositiveFamily0_disjoint_family1 s r,
      cmoPositiveFamily0_disjoint_family2 s r⟩

theorem cmoSpur_not_positive (s r : ℕ) (hs : 1 ≤ s) :
    cmoSpurCell s r ∉ cmoSideFiveCells s r := by
  rw [mem_cmoSideFiveCells_iff s r hs]
  simp [cmoSpurCell, inBenzel, neighboringCell]
  omega

theorem cmoSpur_not_negative (s r : ℕ) (hs : 1 ≤ s) :
    cmoSpurCell s r ∉ cmoSideFiveNegativeCells s r := by
  rw [mem_cmoSideFiveNegativeCells_iff s r hs]
  simp [cmoSpurCell, inBenzel, neighboringCell]
  omega

theorem cmoWalkForwardSideFiveCells_eq (s r : ℕ) :
    cmoWalkForwardSideFiveCells s r =
      cmoSpurCell s r :: cmoSideFiveCells s r := by
  simp [cmoWalkForwardSideFiveCells, cmoSpurCell, cmoSideFiveCells,
    cmoPositiveFamily0, cmoPositiveFamily1, cmoPositiveFamily2]

theorem cmoWalkForwardSideFiveCells_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoWalkForwardSideFiveCells s r).Nodup := by
  rw [cmoWalkForwardSideFiveCells_eq]
  exact List.nodup_cons.mpr
    ⟨cmoSpur_not_positive s r hs, cmoSideFiveCells_nodup s r⟩

theorem mem_cmoWalkReverseSideFiveCells_iff
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    cell ∈ cmoWalkReverseSideFiveCells s r ↔
      cell = cmoSpurCell s r ∨
        cell ∈ cmoSideFiveNegativeCells s r := by
  rcases cell with ⟨i, j⟩
  simp [cmoWalkReverseSideFiveCells, cmoSideFiveNegativeCells,
    cmoNegativeFamily0, cmoNegativeFamily1, cmoNegativeFamily2,
    cmoNegativeFamily3, cmoSpurCell, Prod.mk.injEq]
  constructor
  · rintro (⟨q, hq, h | h⟩ | h | ⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · right; left; exact ⟨q, hq, Or.inl h⟩
    · right; left; exact ⟨q, hq, Or.inr h⟩
    · right; right; left; exact h
    · by_cases he : q = s - 1
      · subst q; left
        push_cast [Nat.cast_sub hs] at h ⊢
        omega
      · right; right; right; left
        exact ⟨q, by omega, h⟩
    · right; right; right; right
      exact ⟨q, hq, h⟩
  · rintro (h | ⟨q, hq, h | h⟩ | h | ⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · right; right; left
      refine ⟨s - 1, by omega, ?_⟩
      push_cast [Nat.cast_sub hs] at h ⊢
      omega
    · left; exact ⟨q, hq, Or.inl h⟩
    · left; exact ⟨q, hq, Or.inr h⟩
    · right; left; exact h
    · right; right; left; exact ⟨q, by omega, h⟩
    · right; right; right; exact ⟨q, hq, h⟩

theorem cmoNegativeFamily0_nodup (s r : ℕ) :
    (cmoNegativeFamily0 s r).Nodup := by
  unfold cmoNegativeFamily0
  rw [List.nodup_flatMap]
  constructor
  · intro q hq
    simp
    omega
  · apply (List.pairwise_lt_range r).imp
    intro a b hab
    simp [Function.onFun, List.disjoint_left]
    omega

theorem cmoNegativeFamily2_nodup (s r : ℕ) :
    (cmoNegativeFamily2 s r).Nodup := by
  unfold cmoNegativeFamily2
  apply (List.nodup_range (s - 1)).map
  intro a b h
  have hfst := congrArg Prod.fst h
  simp only [Function.comp_apply] at hfst
  omega

theorem cmoNegativeFamily3_nodup (s r : ℕ) :
    (cmoNegativeFamily3 s r).Nodup := by
  unfold cmoNegativeFamily3
  apply (List.nodup_range s).map
  intro a b h
  have hfst := congrArg Prod.fst h
  simp only [Function.comp_apply] at hfst
  omega

theorem cmoNegativeFamily0_disjoint_family1 (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily0 s r) (cmoNegativeFamily1 s r) := by
  simp [cmoNegativeFamily0, cmoNegativeFamily1, List.disjoint_left]
  omega

theorem cmoNegativeFamily0_disjoint_family2 (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily0 s r) (cmoNegativeFamily2 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h2
  simp [cmoNegativeFamily0, cmoNegativeFamily2] at h0 h2
  rcases h0 with ⟨a, ha, h | h⟩ <;> rcases h2 with ⟨b, hb, h2⟩
  all_goals have heq := h.symm.trans h2.symm
  all_goals have hfst := congrArg Prod.fst heq
  all_goals have hsnd := congrArg Prod.snd heq
  all_goals simp at hfst hsnd
  all_goals omega

theorem cmoNegativeFamily0_disjoint_family3 (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily0 s r) (cmoNegativeFamily3 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h3
  simp [cmoNegativeFamily0, cmoNegativeFamily3] at h0 h3
  rcases h0 with ⟨a, ha, h | h⟩ <;> rcases h3 with ⟨b, hb, h3⟩
  all_goals have heq := h.symm.trans h3.symm
  all_goals have hfst := congrArg Prod.fst heq
  all_goals have hsnd := congrArg Prod.snd heq
  all_goals simp at hfst hsnd
  all_goals omega

theorem cmoNegativeFamily1_disjoint_family2 (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily1 s r) (cmoNegativeFamily2 s r) := by
  simp [cmoNegativeFamily1, cmoNegativeFamily2, List.disjoint_left]
  omega

theorem cmoNegativeFamily1_disjoint_family3 (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily1 s r) (cmoNegativeFamily3 s r) := by
  simp [cmoNegativeFamily1, cmoNegativeFamily3, List.disjoint_left]
  omega

theorem cmoNegativeFamily2_disjoint_family3 (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily2 s r) (cmoNegativeFamily3 s r) := by
  rw [List.disjoint_left]
  intro cell h2 h3
  simp [cmoNegativeFamily2, cmoNegativeFamily3] at h2 h3
  rcases h2 with ⟨a, ha, h2⟩
  rcases h3 with ⟨b, hb, h3⟩
  have heq := h2.trans h3.symm
  have hfst := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  simp at hfst hsnd
  omega

theorem cmoSideFiveNegativeCells_nodup (s r : ℕ) :
    (cmoSideFiveNegativeCells s r).Nodup := by
  rw [cmoSideFiveNegativeCells, List.nodup_append]
  constructor
  · exact cmoNegativeFamily0_nodup s r
  constructor
  · rw [List.nodup_append]
    constructor
    · simp [cmoNegativeFamily1]
    constructor
    · rw [List.nodup_append]
      exact ⟨cmoNegativeFamily2_nodup s r,
        cmoNegativeFamily3_nodup s r,
        cmoNegativeFamily2_disjoint_family3 s r⟩
    · rw [List.disjoint_append_right]
      exact ⟨cmoNegativeFamily1_disjoint_family2 s r,
        cmoNegativeFamily1_disjoint_family3 s r⟩
  · rw [List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨cmoNegativeFamily0_disjoint_family1 s r,
      cmoNegativeFamily0_disjoint_family2 s r,
      cmoNegativeFamily0_disjoint_family3 s r⟩

def cmoNegativeFamily2Full (s r : ℕ) : List Cell :=
  (List.range s).map fun q : ℕ =>
    (-((s : ℤ)) + 2 + 2 * q, -((r : ℤ)) - 1 - q)

theorem cmoNegativeFamily2Full_nodup (s r : ℕ) :
    (cmoNegativeFamily2Full s r).Nodup := by
  unfold cmoNegativeFamily2Full
  apply (List.nodup_range s).map
  intro a b h
  have hfst := congrArg Prod.fst h
  simp only [Function.comp_apply] at hfst
  omega

theorem cmoNegativeFamily0_disjoint_family2Full (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily0 s r) (cmoNegativeFamily2Full s r) := by
  rw [List.disjoint_left]
  intro cell h0 h2
  simp [cmoNegativeFamily0, cmoNegativeFamily2Full] at h0 h2
  rcases h0 with ⟨a, ha, h | h⟩ <;> rcases h2 with ⟨b, hb, h2⟩
  all_goals have heq := h.symm.trans h2.symm
  all_goals have hfst := congrArg Prod.fst heq
  all_goals have hsnd := congrArg Prod.snd heq
  all_goals simp at hfst hsnd
  all_goals omega

theorem cmoNegativeFamily1_disjoint_family2Full (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily1 s r) (cmoNegativeFamily2Full s r) := by
  simp [cmoNegativeFamily1, cmoNegativeFamily2Full, List.disjoint_left]
  omega

theorem cmoNegativeFamily2Full_disjoint_family3 (s r : ℕ) :
    List.Disjoint (cmoNegativeFamily2Full s r) (cmoNegativeFamily3 s r) := by
  rw [List.disjoint_left]
  intro cell h2 h3
  simp [cmoNegativeFamily2Full, cmoNegativeFamily3] at h2 h3
  rcases h2 with ⟨a, ha, h2⟩
  rcases h3 with ⟨b, hb, h3⟩
  have heq := h2.trans h3.symm
  have hfst := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  simp at hfst hsnd
  omega

theorem cmoWalkReverseSideFiveCells_as_families (s r : ℕ) :
    cmoWalkReverseSideFiveCells s r =
      cmoNegativeFamily0 s r ++
        (cmoNegativeFamily1 s r ++
          (cmoNegativeFamily2Full s r ++ cmoNegativeFamily3 s r)) := by
  simp [cmoWalkReverseSideFiveCells, cmoNegativeFamily0,
    cmoNegativeFamily1, cmoNegativeFamily2Full, cmoNegativeFamily3]

theorem cmoWalkReverseSideFiveCells_nodup (s r : ℕ) :
    (cmoWalkReverseSideFiveCells s r).Nodup := by
  rw [cmoWalkReverseSideFiveCells_as_families, List.nodup_append]
  constructor
  · exact cmoNegativeFamily0_nodup s r
  constructor
  · rw [List.nodup_append]
    constructor
    · simp [cmoNegativeFamily1]
    constructor
    · rw [List.nodup_append]
      exact ⟨cmoNegativeFamily2Full_nodup s r,
        cmoNegativeFamily3_nodup s r,
        cmoNegativeFamily2Full_disjoint_family3 s r⟩
    · rw [List.disjoint_append_right]
      exact ⟨cmoNegativeFamily1_disjoint_family2Full s r,
        cmoNegativeFamily1_disjoint_family3 s r⟩
  · rw [List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨cmoNegativeFamily0_disjoint_family1 s r,
      cmoNegativeFamily0_disjoint_family2Full s r,
      cmoNegativeFamily0_disjoint_family3 s r⟩

end FiniteDefects
