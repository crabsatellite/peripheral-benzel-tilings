import FiniteDefects.D4BallotWordInjectivity

/-!
# Surjectivity onto content-correct ballot words
-/

namespace FiniteDefects

theorem exists_recursiveBallot_of_sequence {word : List BallotMove}
    (h : IsBallotSequence word) :
    ∃ path : RecursiveBallot (majorityCount word) (minorityCount word),
      recursiveBallotWord path = word := by
  induction h with
  | nil =>
      refine ⟨recursiveBallotZeroZeroEquiv.symm PUnit.unit, ?_⟩
      simp [recursiveBallotWord, recursiveBallotData,
        recursiveBallotZeroZeroEquiv, majorityCount, minorityCount]
  | @appendMajority word h ih =>
      obtain ⟨path, hword⟩ := ih
      have hMajorAppend :
          majorityCount (word ++ [.majority]) = majorityCount word + 1 := by
        simp [majorityCount]
      have hMinorAppend :
          minorityCount (word ++ [.majority]) = minorityCount word := by
        simp [minorityCount]
      cases hminor : minorityCount word with
      | zero =>
          let raw := (recursiveBallotSuccZeroEquiv (majorityCount word)).symm
            PUnit.unit
          let target := recastRecursiveBallot hMajorAppend
            (hMinorAppend.trans hminor) raw
          let path0 := recastRecursiveBallot rfl hminor.symm path
          refine ⟨target, ?_⟩
          rw [recursiveBallotWord_recast]
          have hpath0Word : recursiveBallotWord path0 = word := by
            rw [recursiveBallotWord_recast]
            exact hword
          have hpathReplicate :
              recursiveBallotWord path0 =
                List.replicate (majorityCount word) .majority := by
            exact recursiveBallotWord_zero_down (majorityCount word) path0
          have hraw : recursiveBallotWord raw =
              List.replicate (majorityCount word + 1) .majority := by
            simpa [raw] using recursiveBallotWord_succZero
              (majorityCount word) raw
          rw [hraw]
          rw [show List.replicate (majorityCount word + 1) BallotMove.majority =
              List.replicate (majorityCount word) .majority ++ [.majority] by
            simpa using List.replicate_add (majorityCount word) 1
              BallotMove.majority]
          rw [← hpathReplicate, hpath0Word]
      | succ down =>
          have hdu : down ≤ majorityCount word := by
            have hcount := h.count_le
            rw [hminor] at hcount
            omega
          let predecessor := recastRecursiveBallot rfl hminor.symm path
          let raw :=
            (recursiveBallotSuccSuccEquiv (majorityCount word) down hdu).symm
              (.inl predecessor)
          let target := recastRecursiveBallot hMajorAppend
            (hMinorAppend.trans hminor) raw
          refine ⟨target, ?_⟩
          rw [recursiveBallotWord_recast]
          rw [recursiveBallotWord_succSucc_inl]
          rw [recursiveBallotWord_recast]
          exact congrArg (· ++ [.majority]) hword
  | @appendMinority word h hstrict ih =>
      obtain ⟨path, hword⟩ := ih
      have hMajorAppend :
          majorityCount (word ++ [.minority]) = majorityCount word := by
        simp [majorityCount]
      have hMinorAppend :
          minorityCount (word ++ [.minority]) = minorityCount word + 1 := by
        simp [minorityCount]
      have hpositive : 0 < majorityCount word := by omega
      obtain ⟨up, hmajor⟩ := Nat.exists_eq_succ_of_ne_zero hpositive.ne'
      have hdu : minorityCount word ≤ up := by omega
      let predecessor := recastRecursiveBallot hmajor.symm rfl path
      let raw :=
        (recursiveBallotSuccSuccEquiv up (minorityCount word) hdu).symm
          (.inr predecessor)
      let target := recastRecursiveBallot (hMajorAppend.trans hmajor)
        hMinorAppend raw
      refine ⟨target, ?_⟩
      rw [recursiveBallotWord_recast]
      rw [recursiveBallotWord_succSucc_inr]
      rw [recursiveBallotWord_recast]
      exact congrArg (· ++ [.minority]) hword

structure ConcreteBallotWord (up down : ℕ) where
  word : List BallotMove
  majority_eq : majorityCount word = up
  minority_eq : minorityCount word = down
  ballot : IsBallotSequence word

theorem ConcreteBallotWord.ext {up down : ℕ}
    {left right : ConcreteBallotWord up down}
    (hword : left.word = right.word) : left = right := by
  cases left
  cases right
  simp_all

def recursiveBallotToConcrete {up down : ℕ}
    (path : RecursiveBallot up down) : ConcreteBallotWord up down where
  word := recursiveBallotWord path
  majority_eq := recursiveBallotWord_majority path
  minority_eq := recursiveBallotWord_minority path
  ballot := recursiveBallotWord_isBallot path

noncomputable def concreteToRecursiveBallot {up down : ℕ}
    (data : ConcreteBallotWord up down) : RecursiveBallot up down :=
  let raw := (exists_recursiveBallot_of_sequence data.ballot).choose
  recastRecursiveBallot data.majority_eq.symm data.minority_eq.symm raw

theorem concreteToRecursiveBallot_word {up down : ℕ}
    (data : ConcreteBallotWord up down) :
    recursiveBallotWord (concreteToRecursiveBallot data) = data.word := by
  rw [concreteToRecursiveBallot, recursiveBallotWord_recast]
  exact (exists_recursiveBallot_of_sequence data.ballot).choose_spec

noncomputable def recursiveBallotEquivConcrete (up down : ℕ) :
    RecursiveBallot up down ≃ ConcreteBallotWord up down where
  toFun := recursiveBallotToConcrete
  invFun := concreteToRecursiveBallot
  left_inv := by
    intro path
    apply recursiveBallotWord_injective up down
    exact concreteToRecursiveBallot_word (recursiveBallotToConcrete path)
  right_inv := by
    intro data
    apply ConcreteBallotWord.ext
    exact concreteToRecursiveBallot_word data

end FiniteDefects
