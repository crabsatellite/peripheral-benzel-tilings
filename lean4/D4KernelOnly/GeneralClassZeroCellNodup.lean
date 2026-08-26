import D4KernelOnly.GeneralClassZeroBoundaryCells

/-! # Duplicate-free class-zero side-five cell lists -/

namespace FiniteDefects

open BenzelProblem6Kernel

def czRawForward0 (s r : ℕ) : List Cell :=
  (List.range r).map fun q : ℕ =>
    ((r : ℤ) - 2 * q - 2, (s : ℤ) + q + 1)

def czRawReverse0 (s r : ℕ) : List Cell :=
  (List.range s).map fun q : ℕ =>
    (-((r : ℤ)) - q, (s : ℤ) + r - q)

theorem czRawForward0_nodup (s r : ℕ) : (czRawForward0 s r).Nodup := by
  unfold czRawForward0
  apply (List.nodup_range r).map
  intro a b h
  have hcoord := congrArg Prod.snd h
  simp at hcoord
  omega

theorem czPositiveFamily1_nodup (s r : ℕ) : (czPositiveFamily1 s r).Nodup := by
  unfold czPositiveFamily1
  apply (List.nodup_range r).map
  intro a b h
  have hcoord := congrArg Prod.fst h
  simp at hcoord
  omega

theorem czPositiveFamily2_nodup (s r : ℕ) : (czPositiveFamily2 s r).Nodup := by
  unfold czPositiveFamily2
  rw [List.nodup_flatMap]
  constructor
  · intro q hq
    simp
  · apply (List.pairwise_lt_range s).imp
    intro a b hab
    simp [Function.onFun, List.disjoint_left]
    omega

theorem czRawForward0_disjoint_family1 (s r : ℕ) :
    List.Disjoint (czRawForward0 s r) (czPositiveFamily1 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h1
  simp [czRawForward0, czPositiveFamily1] at h0 h1
  rcases h0 with ⟨a, ha, rfl⟩
  rcases h1 with ⟨b, hb, h⟩
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp at hfst hsnd
  omega

theorem czRawForward0_disjoint_family2 (s r : ℕ) :
    List.Disjoint (czRawForward0 s r) (czPositiveFamily2 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h2
  simp [czRawForward0, czPositiveFamily2] at h0 h2
  rcases h0 with ⟨a, ha, rfl⟩
  rcases h2 with ⟨b, hb, h | h⟩
  all_goals have hfst := congrArg Prod.fst h
  all_goals have hsnd := congrArg Prod.snd h
  all_goals simp at hfst hsnd
  all_goals omega

theorem czPositiveFamily1_disjoint_family2 (s r : ℕ) :
    List.Disjoint (czPositiveFamily1 s r) (czPositiveFamily2 s r) := by
  rw [List.disjoint_left]
  intro cell h1 h2
  simp [czPositiveFamily1, czPositiveFamily2] at h1 h2
  rcases h1 with ⟨a, ha, rfl⟩
  rcases h2 with ⟨b, hb, h | h⟩
  all_goals have hfst := congrArg Prod.fst h
  all_goals have hsnd := congrArg Prod.snd h
  all_goals simp at hfst hsnd
  all_goals omega

theorem czWalkForwardSideFiveCells_nodup (s r : ℕ) :
    (czWalkForwardSideFiveCells s r).Nodup := by
  change ((czRawForward0 s r ++ czPositiveFamily1 s r) ++
    czPositiveFamily2 s r).Nodup
  rw [List.append_assoc]
  rw [List.nodup_append, List.nodup_append, List.disjoint_append_right]
  exact ⟨czRawForward0_nodup s r,
    ⟨czPositiveFamily1_nodup s r, czPositiveFamily2_nodup s r,
      czPositiveFamily1_disjoint_family2 s r⟩,
    czRawForward0_disjoint_family1 s r,
    czRawForward0_disjoint_family2 s r⟩

theorem czRawReverse0_nodup (s r : ℕ) : (czRawReverse0 s r).Nodup := by
  unfold czRawReverse0
  apply (List.nodup_range s).map
  intro a b h
  have hcoord := congrArg Prod.fst h
  simp at hcoord
  omega

theorem czNegativeFamily1_nodup (s r : ℕ) : (czNegativeFamily1 s r).Nodup := by
  unfold czNegativeFamily1
  rw [List.nodup_flatMap]
  constructor
  · intro q hq
    simp
  · apply (List.pairwise_lt_range r).imp
    intro a b hab
    simp [Function.onFun, List.disjoint_left]
    omega

theorem czNegativeFamily2_nodup (s r : ℕ) : (czNegativeFamily2 s r).Nodup := by
  unfold czNegativeFamily2
  apply (List.nodup_range s).map
  intro a b h
  have hcoord := congrArg Prod.snd h
  simp at hcoord
  omega

theorem czRawReverse0_disjoint_family1 (s r : ℕ) :
    List.Disjoint (czRawReverse0 s r) (czNegativeFamily1 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h1
  simp [czRawReverse0, czNegativeFamily1] at h0 h1
  rcases h0 with ⟨a, ha, rfl⟩
  rcases h1 with ⟨b, hb, h | h⟩
  all_goals have hfst := congrArg Prod.fst h
  all_goals have hsnd := congrArg Prod.snd h
  all_goals simp at hfst hsnd
  all_goals omega

theorem czRawReverse0_disjoint_family2 (s r : ℕ) :
    List.Disjoint (czRawReverse0 s r) (czNegativeFamily2 s r) := by
  rw [List.disjoint_left]
  intro cell h0 h2
  simp [czRawReverse0, czNegativeFamily2] at h0 h2
  rcases h0 with ⟨a, ha, rfl⟩
  rcases h2 with ⟨b, hb, h⟩
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp at hfst hsnd
  omega

theorem czNegativeFamily1_disjoint_family2 (s r : ℕ) :
    List.Disjoint (czNegativeFamily1 s r) (czNegativeFamily2 s r) := by
  rw [List.disjoint_left]
  intro cell h1 h2
  simp [czNegativeFamily1, czNegativeFamily2] at h1 h2
  rcases h1 with ⟨a, ha, h | h⟩
  all_goals rcases h2 with ⟨b, hb, h2⟩
  all_goals have heq := h.symm.trans h2.symm
  all_goals have hfst := congrArg Prod.fst heq
  all_goals have hsnd := congrArg Prod.snd heq
  all_goals simp at hfst hsnd
  all_goals omega

theorem czWalkReverseSideFiveCells_nodup (s r : ℕ) :
    (czWalkReverseSideFiveCells s r).Nodup := by
  change ((czRawReverse0 s r ++ czNegativeFamily1 s r) ++
    czNegativeFamily2 s r).Nodup
  rw [List.append_assoc]
  rw [List.nodup_append, List.nodup_append, List.disjoint_append_right]
  exact ⟨czRawReverse0_nodup s r,
    ⟨czNegativeFamily1_nodup s r, czNegativeFamily2_nodup s r,
      czNegativeFamily1_disjoint_family2 s r⟩,
    czRawReverse0_disjoint_family1 s r,
    czRawReverse0_disjoint_family2 s r⟩

theorem czSpur_not_positive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    czSpurCell s r ∉ czSideFiveCells s r := by
  rw [mem_czSideFiveCells_iff s r hs hr]
  simp [czSpurCell, inBenzel, neighboringCell]
  omega

theorem czSpur_not_negative
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    czSpurCell s r ∉ czSideFiveNegativeCells s r := by
  rw [mem_czSideFiveNegativeCells_iff s r hs hr]
  simp [czSpurCell, inBenzel, neighboringCell]
  omega

theorem mem_czWalkForwardSideFiveCells_iff
    (s r : ℕ) (hr : 1 ≤ r) (cell : Cell) :
    cell ∈ czWalkForwardSideFiveCells s r ↔
      cell = czSpurCell s r ∨ cell ∈ czSideFiveCells s r := by
  rcases cell with ⟨i, j⟩
  simp [czWalkForwardSideFiveCells, czSideFiveCells,
    czPositiveFamily0, czPositiveFamily1, czPositiveFamily2,
    czSpurCell, Prod.mk.injEq, List.mem_flatMap]
  constructor
  · rintro (⟨q, hq, h⟩ | h)
    by_cases he : q = r - 1
    · left
      subst q
      push_cast [Nat.cast_sub hr] at h ⊢
      omega
    · right; left
      exact ⟨q, by omega, h⟩
    · rcases h with h1 | h2
      · right; right; left; exact h1
      · right; right; right; exact h2
  · rintro (h | ⟨q, hq, h⟩ | h)
    · left
      refine ⟨r - 1, by omega, ?_⟩
      push_cast [Nat.cast_sub hr] at h ⊢
      omega
    · left; exact ⟨q, by omega, h⟩
    · right; exact h

theorem mem_czWalkReverseSideFiveCells_iff
    (s r : ℕ) (hs : 1 ≤ s) (cell : Cell) :
    cell ∈ czWalkReverseSideFiveCells s r ↔
      cell = czSpurCell s r ∨ cell ∈ czSideFiveNegativeCells s r := by
  rcases cell with ⟨i, j⟩
  simp [czWalkReverseSideFiveCells, czSideFiveNegativeCells,
    czNegativeFamily0, czNegativeFamily1, czNegativeFamily2,
    czSpurCell, Prod.mk.injEq, List.mem_flatMap]
  constructor
  · rintro (⟨q, hq, h⟩ | h)
    by_cases he : q = 0
    · left
      subst q
      omega
    · right; left
      refine ⟨q - 1, by omega, ?_⟩
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at h ⊢
      omega
    · rcases h with h1 | h2
      · right; right; left; exact h1
      · right; right; right; exact h2
  · rintro (h | ⟨q, hq, h⟩ | h)
    · left
      exact ⟨0, hs, by omega⟩
    · left
      refine ⟨q + 1, by omega, ?_⟩
      push_cast
      omega
    · right; exact h

end FiniteDefects
