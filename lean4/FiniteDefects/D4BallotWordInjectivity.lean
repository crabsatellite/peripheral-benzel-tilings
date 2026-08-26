import FiniteDefects.D4BallotWords

/-!
# Cast-free views of recursive ballot states
-/

namespace FiniteDefects

def recastRecursiveBallot {up down up' down' : ℕ}
    (hup : up = up') (hdown : down = down')
    (path : RecursiveBallot up' down') : RecursiveBallot up down :=
  Equiv.cast (congrArg₂ RecursiveBallot hup hdown).symm path

theorem recursiveBallotWord_recast {up down up' down' : ℕ}
    (hup : up = up') (hdown : down = down')
    (path : RecursiveBallot up' down') :
    recursiveBallotWord (recastRecursiveBallot hup hdown path) =
      recursiveBallotWord path := by
  subst up'
  subst down'
  rfl

def recursiveBallotZeroZeroEquiv : RecursiveBallot 0 0 ≃ PUnit :=
  Equiv.cast (by simp [RecursiveBallot])

def recursiveBallotSuccZeroEquiv (up : ℕ) :
    RecursiveBallot (up + 1) 0 ≃ PUnit :=
  Equiv.cast (by simp [RecursiveBallot])

theorem recursiveBallotWord_succZero (up : ℕ)
    (path : RecursiveBallot (up + 1) 0) :
    recursiveBallotWord path = List.replicate (up + 1) .majority := by
  simp [recursiveBallotWord, recursiveBallotData]

theorem recursiveBallotWord_zero_down (up : ℕ)
    (path : RecursiveBallot up 0) :
    recursiveBallotWord path = List.replicate up .majority := by
  cases up with
  | zero => simp [recursiveBallotWord, recursiveBallotData]
  | succ up => simpa using recursiveBallotWord_succZero up path

def recursiveBallotSuccSuccEquiv (up down : ℕ) (hdu : down ≤ up) :
    RecursiveBallot (up + 1) (down + 1) ≃
      (RecursiveBallot up (down + 1) ⊕ RecursiveBallot (up + 1) down) :=
  Equiv.cast (by simp [RecursiveBallot, hdu])

theorem recursiveBallotWord_succSucc_inl (up down : ℕ) (hdu : down ≤ up)
    (path : RecursiveBallot up (down + 1)) :
    recursiveBallotWord ((recursiveBallotSuccSuccEquiv up down hdu).symm (.inl path)) =
      recursiveBallotWord path ++ [.majority] := by
  have hdec : down.decLe up = isTrue hdu := Subsingleton.elim _ _
  simp [recursiveBallotWord, recursiveBallotData, recursiveBallotSuccSuccEquiv,
    RecursiveBallot, hdu, hdec]

theorem recursiveBallotWord_succSucc_inr (up down : ℕ) (hdu : down ≤ up)
    (path : RecursiveBallot (up + 1) down) :
    recursiveBallotWord ((recursiveBallotSuccSuccEquiv up down hdu).symm (.inr path)) =
      recursiveBallotWord path ++ [.minority] := by
  have hdec : down.decLe up = isTrue hdu := Subsingleton.elim _ _
  simp [recursiveBallotWord, recursiveBallotData, recursiveBallotSuccSuccEquiv,
    RecursiveBallot, hdu, hdec]

theorem recursiveBallotWord_injective :
    (up down : ℕ) → Function.Injective (@recursiveBallotWord up down)
  | 0, 0 => by
      intro left right _
      apply recursiveBallotZeroZeroEquiv.injective
      exact Subsingleton.elim _ _
  | 0, down + 1 => by
      intro left
      have htype := recursiveBallot_eq_empty_of_lt
        (show 0 < down + 1 by omega)
      exact Empty.elim (Equiv.cast htype left)
  | up + 1, 0 => by
      intro left right _
      apply (recursiveBallotSuccZeroEquiv up).injective
      exact Subsingleton.elim _ _
  | up + 1, down + 1 => by
      intro left right heq
      by_cases hdu : down ≤ up
      · let e := recursiveBallotSuccSuccEquiv up down hdu
        rcases hleft : e left with leftPath | leftPath <;>
          rcases hright : e right with rightPath | rightPath
        · have leftrepr : left = e.symm (.inl leftPath) := by
            apply e.injective
            simp [hleft]
          have rightrepr : right = e.symm (.inl rightPath) := by
            apply e.injective
            simp [hright]
          rw [leftrepr, rightrepr,
            recursiveBallotWord_succSucc_inl,
            recursiveBallotWord_succSucc_inl] at heq
          have hpEq : leftPath = rightPath := by
            apply recursiveBallotWord_injective up (down + 1)
            exact List.append_cancel_right heq
          rw [leftrepr, rightrepr, hpEq]
        · have leftrepr : left = e.symm (.inl leftPath) := by
            apply e.injective
            simp [hleft]
          have rightrepr : right = e.symm (.inr rightPath) := by
            apply e.injective
            simp [hright]
          rw [leftrepr, rightrepr,
            recursiveBallotWord_succSucc_inl,
            recursiveBallotWord_succSucc_inr] at heq
          have hreversed := congrArg List.reverse heq
          simp at hreversed
        · have leftrepr : left = e.symm (.inr leftPath) := by
            apply e.injective
            simp [hleft]
          have rightrepr : right = e.symm (.inl rightPath) := by
            apply e.injective
            simp [hright]
          rw [leftrepr, rightrepr,
            recursiveBallotWord_succSucc_inr,
            recursiveBallotWord_succSucc_inl] at heq
          have hreversed := congrArg List.reverse heq
          simp at hreversed
        · have leftrepr : left = e.symm (.inr leftPath) := by
            apply e.injective
            simp [hleft]
          have rightrepr : right = e.symm (.inr rightPath) := by
            apply e.injective
            simp [hright]
          rw [leftrepr, rightrepr,
            recursiveBallotWord_succSucc_inr,
            recursiveBallotWord_succSucc_inr] at heq
          have hpEq : leftPath = rightPath := by
            apply recursiveBallotWord_injective (up + 1) down
            exact List.append_cancel_right heq
          rw [leftrepr, rightrepr, hpEq]
      · have htype : RecursiveBallot (up + 1) (down + 1) = Empty := by
          simp [RecursiveBallot, hdu]
        exact Empty.elim (Equiv.cast htype left)
termination_by up down => up + down

end FiniteDefects
