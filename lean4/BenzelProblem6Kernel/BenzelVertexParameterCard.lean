import BenzelProblem6Kernel.PeripheralIncidenceLength
import Mathlib.Data.Fintype.Sigma

/-! # Finite parameter counts for benzel vertices -/

namespace BenzelProblem6Kernel

def upOneExceptions (t : ℕ) : Finset (SimplexPoint (t + 1)) :=
  {sourceZero (t + 1), sourceOne (t + 1), sourceTwo (t + 1)}

def upTwoExtra₀ (t : ℕ) : SimplexPoint (t + 2) where
  u := 0
  v := 1
  w := t + 1
  sum_eq := by omega

def upTwoExtra₁ (t : ℕ) : SimplexPoint (t + 2) where
  u := 1
  v := t + 1
  w := 0
  sum_eq := by omega

def upTwoExtra₂ (t : ℕ) : SimplexPoint (t + 2) where
  u := t + 1
  v := 0
  w := 1
  sum_eq := by omega

def upTwoExceptions (t : ℕ) : Finset (SimplexPoint (t + 2)) :=
  {sourceZero (t + 2), sourceOne (t + 2), sourceTwo (t + 2),
    upTwoExtra₀ t, upTwoExtra₁ t, upTwoExtra₂ t}

def downZeroExceptions (t : ℕ) : Finset (SimplexPoint (t + 1)) :=
  {sourceZero (t + 1), sourceOne (t + 1)}

def downOneExceptions (t : ℕ) : Finset (SimplexPoint (t + 1)) :=
  {sourceZero (t + 1), sourceTwo (t + 1)}

def downTwoExceptions (t : ℕ) : Finset (SimplexPoint (t + 1)) :=
  {sourceOne (t + 1), sourceTwo (t + 1)}

theorem card_upOneExceptions (t : ℕ) :
    (upOneExceptions t).card = 3 := by
  simp [upOneExceptions, sourceZero, sourceOne, sourceTwo]

theorem card_upTwoExceptions (t : ℕ) :
    (upTwoExceptions t).card = 6 := by
  simp [upTwoExceptions, sourceZero, sourceOne, sourceTwo,
    upTwoExtra₀, upTwoExtra₁, upTwoExtra₂]

theorem card_downZeroExceptions (t : ℕ) :
    (downZeroExceptions t).card = 2 := by
  simp [downZeroExceptions, sourceZero, sourceOne]

theorem card_downOneExceptions (t : ℕ) :
    (downOneExceptions t).card = 2 := by
  simp [downOneExceptions, sourceZero, sourceTwo]

theorem card_downTwoExceptions (t : ℕ) :
    (downTwoExceptions t).card = 2 := by
  simp [downTwoExceptions, sourceOne, sourceTwo]

abbrev UpOneParameter (t : ℕ) :=
  {p : SimplexPoint (t + 1) // p ∉ upOneExceptions t}

abbrev UpTwoParameter (t : ℕ) :=
  {p : SimplexPoint (t + 2) // p ∉ upTwoExceptions t}

abbrev DownZeroParameter (t : ℕ) :=
  {p : SimplexPoint (t + 1) // p ∉ downZeroExceptions t}

abbrev DownOneParameter (t : ℕ) :=
  {p : SimplexPoint (t + 1) // p ∉ downOneExceptions t}

abbrev DownTwoParameter (t : ℕ) :=
  {p : SimplexPoint (t + 1) // p ∉ downTwoExceptions t}

theorem card_parameter_complement {total : ℕ}
    (exceptions : Finset (SimplexPoint total)) :
    Fintype.card {p : SimplexPoint total // p ∉ exceptions} =
      Fintype.card (SimplexPoint total) - exceptions.card := by
  classical
  rw [Fintype.card_subtype_compl
    (fun p : SimplexPoint total => p ∈ exceptions)]
  simp

theorem card_upOneParameter (t : ℕ) :
    Fintype.card (UpOneParameter t) = (t + 3).choose 2 - 3 := by
  rw [card_parameter_complement, card_simplexPoint,
    card_upOneExceptions]

theorem card_upTwoParameter (t : ℕ) :
    Fintype.card (UpTwoParameter t) = (t + 4).choose 2 - 6 := by
  rw [card_parameter_complement, card_simplexPoint,
    card_upTwoExceptions]

theorem card_downZeroParameter (t : ℕ) :
    Fintype.card (DownZeroParameter t) = (t + 3).choose 2 - 2 := by
  rw [card_parameter_complement, card_simplexPoint,
    card_downZeroExceptions]

theorem card_downOneParameter (t : ℕ) :
    Fintype.card (DownOneParameter t) = (t + 3).choose 2 - 2 := by
  rw [card_parameter_complement, card_simplexPoint,
    card_downOneExceptions]

theorem card_downTwoParameter (t : ℕ) :
    Fintype.card (DownTwoParameter t) = (t + 3).choose 2 - 2 := by
  rw [card_parameter_complement, card_simplexPoint,
    card_downTwoExceptions]

abbrev UpVertexParameter (t : ℕ) :=
  SimplexPoint t ⊕ UpOneParameter t ⊕ UpTwoParameter t

abbrev DownVertexParameter (t : ℕ) :=
  DownZeroParameter t ⊕ DownOneParameter t ⊕ DownTwoParameter t

theorem card_upVertexParameter (t : ℕ) :
    Fintype.card (UpVertexParameter t) =
      (t + 2).choose 2 + ((t + 3).choose 2 - 3) +
        ((t + 4).choose 2 - 6) := by
  rw [Fintype.card_sum, Fintype.card_sum,
    card_simplexPoint, card_upOneParameter, card_upTwoParameter]
  omega

theorem card_downVertexParameter (t : ℕ) :
    Fintype.card (DownVertexParameter t) =
      3 * ((t + 3).choose 2 - 2) := by
  rw [Fintype.card_sum, Fintype.card_sum,
    card_downZeroParameter, card_downOneParameter,
    card_downTwoParameter]
  omega

end BenzelProblem6Kernel
