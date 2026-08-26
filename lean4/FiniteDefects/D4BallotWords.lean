import FiniteDefects.D4BallotRecurrence
import Mathlib.Data.List.Infix

/-!
# Concrete words carried by recursive ballot paths
-/

namespace FiniteDefects

inductive BallotMove
  | majority
  | minority
  deriving DecidableEq, Repr

def majorityCount (word : List BallotMove) : ℕ :=
  word.count .majority

def minorityCount (word : List BallotMove) : ℕ :=
  word.count .minority

inductive IsBallotSequence : List BallotMove → Prop
  | nil : IsBallotSequence []
  | appendMajority {word : List BallotMove} :
      IsBallotSequence word → IsBallotSequence (word ++ [.majority])
  | appendMinority {word : List BallotMove} :
      IsBallotSequence word →
      minorityCount word < majorityCount word →
      IsBallotSequence (word ++ [.minority])

theorem IsBallotSequence.count_le {word : List BallotMove}
    (h : IsBallotSequence word) :
    minorityCount word ≤ majorityCount word := by
  induction h with
  | nil => simp [minorityCount, majorityCount]
  | @appendMajority word h ih =>
      have ih' : List.count BallotMove.minority word ≤
          List.count BallotMove.majority word := by
        simpa [minorityCount, majorityCount] using ih
      simp only [minorityCount, majorityCount, List.count_append,
        List.count_cons, List.count_nil]
      simp
      omega
  | @appendMinority word h hstrict ih =>
      have hstrict' : List.count BallotMove.minority word <
          List.count BallotMove.majority word := by
        simpa [minorityCount, majorityCount] using hstrict
      simp only [minorityCount, majorityCount, List.count_append,
        List.count_cons, List.count_nil]
      simp
      omega

theorem IsBallotSequence.prefix_closed {pre word : List BallotMove}
    (hword : IsBallotSequence word) (hp : pre <+: word) :
    IsBallotSequence pre := by
  induction hword with
  | nil =>
      have hlen := hp.length_le
      have hzero : pre.length = 0 := by simpa using hlen
      have hempty : pre = [] := List.length_eq_zero.mp hzero
      subst pre
      exact IsBallotSequence.nil
  | @appendMajority word h ih =>
      by_cases hlength : pre.length ≤ word.length
      · have hpword : pre <+: word := by
          exact (List.isPrefix_append_of_length
            (l₁ := pre) (l₂ := word) (l₃ := [BallotMove.majority]) hlength).mp hp
        exact ih hpword
      · have hpLength : pre.length = (word ++ [BallotMove.majority]).length := by
          have hpLe := hp.length_le
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.add_zero] at hpLe
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.add_zero]
          omega
        rw [hp.eq_of_length hpLength]
        exact IsBallotSequence.appendMajority h
  | @appendMinority word h hstrict ih =>
      by_cases hlength : pre.length ≤ word.length
      · have hpword : pre <+: word := by
          exact (List.isPrefix_append_of_length
            (l₁ := pre) (l₂ := word) (l₃ := [BallotMove.minority]) hlength).mp hp
        exact ih hpword
      · have hpLength : pre.length = (word ++ [BallotMove.minority]).length := by
          have hpLe := hp.length_le
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.add_zero] at hpLe
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.add_zero]
          omega
        rw [hp.eq_of_length hpLength]
        exact IsBallotSequence.appendMinority h hstrict

theorem majorityCount_prefix_le {pre word : List BallotMove}
    (hp : pre <+: word) : majorityCount pre ≤ majorityCount word := by
  rcases hp with ⟨tail, rfl⟩
  simp [majorityCount]

theorem minorityCount_prefix_le {pre word : List BallotMove}
    (hp : pre <+: word) : minorityCount pre ≤ minorityCount word := by
  rcases hp with ⟨tail, rfl⟩
  simp [minorityCount]

theorem replicate_majority_isBallot (length : ℕ) :
    IsBallotSequence (List.replicate length .majority) := by
  induction length with
  | zero => exact IsBallotSequence.nil
  | succ length ih =>
      have hrep : List.replicate (length + 1) BallotMove.majority =
          List.replicate length .majority ++ [.majority] := by
        simpa using List.replicate_add length 1 BallotMove.majority
      rw [hrep]
      exact IsBallotSequence.appendMajority ih

structure BallotWordData (up down : ℕ) where
  word : List BallotMove
  length_eq : word.length = up + down
  majority_eq : majorityCount word = up
  minority_eq : minorityCount word = down
  ballot : IsBallotSequence word

def recursiveBallotData :
    (up down : ℕ) → RecursiveBallot up down → BallotWordData up down
  | 0, 0, _ =>
      ⟨[], by simp, by simp [majorityCount], by simp [minorityCount],
        IsBallotSequence.nil⟩
  | 0, _ + 1, path => by
      simp only [RecursiveBallot] at path
      exact Empty.elim path
  | up + 1, 0, _ => by
      refine ⟨List.replicate (up + 1) .majority, by simp, ?_, ?_,
        replicate_majority_isBallot (up + 1)⟩
      · simp [majorityCount]
      · simp [minorityCount, List.count_replicate]
  | up + 1, down + 1, path => by
      simp only [RecursiveBallot] at path
      split at path
      · rcases path with path | path
        · let previous := recursiveBallotData up (down + 1) path
          refine ⟨previous.word ++ [.majority], ?_, ?_, ?_,
            IsBallotSequence.appendMajority previous.ballot⟩
          · simp [previous.length_eq]
            omega
          · simp only [majorityCount, List.count_append, List.count_cons,
              List.count_nil, if_pos, Nat.add_zero]
            simpa [majorityCount] using previous.majority_eq
          · simp only [minorityCount, List.count_append, List.count_cons,
              List.count_nil, if_neg (by decide : BallotMove.majority ≠ .minority),
              Nat.add_zero]
            simpa [minorityCount] using previous.minority_eq
        · let previous := recursiveBallotData (up + 1) down path
          refine ⟨previous.word ++ [.minority], ?_, ?_, ?_, ?_⟩
          · simp [previous.length_eq]
            omega
          · simp only [majorityCount, List.count_append, List.count_cons,
              List.count_nil, if_neg (by decide : BallotMove.minority ≠ .majority),
              Nat.add_zero]
            simpa [majorityCount] using previous.majority_eq
          · simp only [minorityCount, List.count_append, List.count_cons,
              List.count_nil, if_pos, Nat.add_zero]
            simpa [minorityCount] using previous.minority_eq
          · apply IsBallotSequence.appendMinority previous.ballot
            rw [previous.minority_eq, previous.majority_eq]
            omega
      · exact Empty.elim path
termination_by up down _ => up + down

def recursiveBallotWord {up down : ℕ}
    (path : RecursiveBallot up down) : List BallotMove :=
  (recursiveBallotData up down path).word

theorem recursiveBallotWord_length {up down : ℕ}
    (path : RecursiveBallot up down) :
    (recursiveBallotWord path).length = up + down :=
  (recursiveBallotData up down path).length_eq

theorem recursiveBallotWord_majority {up down : ℕ}
    (path : RecursiveBallot up down) :
    majorityCount (recursiveBallotWord path) = up :=
  (recursiveBallotData up down path).majority_eq

theorem recursiveBallotWord_minority {up down : ℕ}
    (path : RecursiveBallot up down) :
    minorityCount (recursiveBallotWord path) = down :=
  (recursiveBallotData up down path).minority_eq

theorem recursiveBallotWord_isBallot {up down : ℕ}
    (path : RecursiveBallot up down) :
    IsBallotSequence (recursiveBallotWord path) :=
  (recursiveBallotData up down path).ballot

theorem recursiveBallotWord_count_le {up down : ℕ}
    (path : RecursiveBallot up down) :
    minorityCount (recursiveBallotWord path) ≤
      majorityCount (recursiveBallotWord path) :=
  (recursiveBallotWord_isBallot path).count_le

theorem recursiveBallotPrefix_count_le {up down : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) :
    minorityCount pre ≤ majorityCount pre :=
  ((recursiveBallotWord_isBallot path).prefix_closed hp).count_le

end FiniteDefects
