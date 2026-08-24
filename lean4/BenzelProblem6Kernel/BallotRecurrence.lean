import BenzelProblem6Kernel.ChiralityCounts
import Mathlib.Data.Fintype.Sum

/-!
# Recursive ballot paths and their cardinality
-/

namespace BenzelProblem6Kernel

def RecursiveBallot : ℕ → ℕ → Type
  | 0, 0 => PUnit
  | 0, _ + 1 => Empty
  | _ + 1, 0 => PUnit
  | up + 1, down + 1 =>
      if down ≤ up then
        RecursiveBallot up (down + 1) ⊕ RecursiveBallot (up + 1) down
      else Empty
termination_by up down => up + down

noncomputable def recursiveBallotFintype :
    (up down : ℕ) → Fintype (RecursiveBallot up down)
  | 0, 0 => by
      simpa only [RecursiveBallot] using (inferInstance : Fintype PUnit)
  | 0, _ + 1 => by
      simpa only [RecursiveBallot] using (inferInstance : Fintype Empty)
  | _ + 1, 0 => by
      simpa only [RecursiveBallot] using (inferInstance : Fintype PUnit)
  | up + 1, down + 1 => by
      simp only [RecursiveBallot]
      split
      · letI := recursiveBallotFintype up (down + 1)
        letI := recursiveBallotFintype (up + 1) down
        infer_instance
      · infer_instance
termination_by up down => up + down

noncomputable instance (up down : ℕ) : Fintype (RecursiveBallot up down) :=
  recursiveBallotFintype up down

theorem recursiveBallot_eq_empty_of_lt {up down : ℕ} (h : up < down) :
    RecursiveBallot up down = Empty := by
  rcases up with _ | up <;> rcases down with _ | down
  · omega
  · simp [RecursiveBallot]
  · omega
  · simp [RecursiveBallot, show ¬down ≤ up by omega]

theorem card_recursiveBallot_eq_zero_of_lt {up down : ℕ} (h : up < down) :
    Fintype.card (RecursiveBallot up down) = 0 := by
  calc
    Fintype.card (RecursiveBallot up down) = Fintype.card Empty :=
      Fintype.card_congr (Equiv.cast (recursiveBallot_eq_empty_of_lt h))
    _ = 0 := by simp

theorem ballotNumber_pascal (up down : ℕ) (hdu : down ≤ up) :
    ballotNumber (up + down + 1) (down + 1) +
        ballotNumber (up + down + 1) down =
      ballotNumber (up + down + 2) (down + 1) := by
  rcases down with _ | down
  · simp [ballotNumber, Nat.choose, Nat.add_comm]
  · let previous := up + down + 2
    let above := previous.choose (down + 2)
    let middle := previous.choose (down + 1)
    let below := previous.choose down
    have habove := Nat.choose_succ_right_eq previous (down + 1)
    have hmiddle := Nat.choose_succ_right_eq previous down
    have hsubAbove : previous - (down + 1) = up + 1 := by
      dsimp [previous]
      omega
    have hsubMiddle : previous - down = up + 2 := by
      dsimp [previous]
      omega
    rw [hsubAbove] at habove
    rw [hsubMiddle] at hmiddle
    have hmiddleAbove : middle ≤ above := by
      apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < down + 2)
      calc
        middle * (down + 2) ≤ middle * (up + 1) := by
          exact Nat.mul_le_mul_left _ (by omega)
        _ = above * (down + 2) := by
          simpa [above, middle] using habove.symm
    have hbelowMiddle : below ≤ middle := by
      apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < down + 1)
      calc
        below * (down + 1) ≤ below * (up + 2) := by
          exact Nat.mul_le_mul_left _ (by omega)
        _ = middle * (down + 1) := by
          simpa [below, middle] using hmiddle.symm
    have hpascalAbove :
        (previous + 1).choose (down + 2) = middle + above := by
      simpa [above, middle] using Nat.choose_succ_succ previous (down + 1)
    have hpascalMiddle :
        (previous + 1).choose (down + 1) = below + middle := by
      simpa [below, middle] using Nat.choose_succ_succ previous down
    simp only [ballotNumber]
    change (above - middle) + (middle - below) =
      (previous + 1).choose (down + 2) -
        (previous + 1).choose (down + 1)
    rw [hpascalAbove, hpascalMiddle]
    omega

theorem card_recursiveBallot_of_le :
    (up down : ℕ) → down ≤ up →
      Fintype.card (RecursiveBallot up down) = ballotNumber (up + down) down
  | 0, 0, _ => by simp [RecursiveBallot, ballotNumber]
  | 0, _ + 1, h => by omega
  | _ + 1, 0, _ => by simp [RecursiveBallot, ballotNumber]
  | up + 1, down + 1, h => by
      have hdu : down ≤ up := by omega
      simp only [RecursiveBallot, if_pos hdu]
      rw [Fintype.card_sum]
      rw [card_recursiveBallot_of_le (up + 1) down (by omega)]
      by_cases hstrict : down < up
      · rw [card_recursiveBallot_of_le up (down + 1) (by omega)]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ballotNumber_pascal up down hdu
      · have heq : down = up := by omega
        have hinvalid : up < down + 1 := by omega
        rw [card_recursiveBallot_eq_zero_of_lt hinvalid]
        rw [zero_add]
        have hleftZero : ballotNumber (up + (down + 1)) (down + 1) = 0 := by
          subst down
          simp only [ballotNumber]
          rw [show up + (up + 1) = 2 * up + 1 by omega]
          rw [Nat.choose_symm_half]
          omega
        have hrecurrence := ballotNumber_pascal up down hdu
        have hnormalized : ballotNumber (up + down + 1) (down + 1) = 0 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hleftZero
        rw [hnormalized, zero_add] at hrecurrence
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrecurrence
termination_by up down _ => up + down

end BenzelProblem6Kernel
