import BenzelProblem6Kernel.ChiralityCounts
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# Developed-sector binary words

A word is represented by the finite set of its minority positions.  This makes
the unrestricted binomial cardinality a direct Mathlib theorem.  The ballot
reflection equivalence is kept as a separate producer.
-/

namespace BenzelProblem6Kernel

abbrev BinaryWord (total down : ℕ) :=
  ↥((Finset.univ : Finset (Fin total)).powersetCard down)

theorem card_binaryWord (total down : ℕ) :
    Fintype.card (BinaryWord total down) = total.choose down := by
  simp [BinaryWord]

abbrev PositiveSectorWords (x y z : ℕ) :=
  BinaryWord (2 * x + y + 2) x ×
  BinaryWord (2 * y + z + 2) y ×
  BinaryWord (2 * z + x + 2) z

theorem card_positiveSectorWords (x y z : ℕ) :
    Fintype.card (PositiveSectorWords x y z) =
      positiveChiralityCount x y z := by
  simp [PositiveSectorWords, positiveChiralityCount, card_binaryWord, mul_assoc]

def prefixMinority {total down : ℕ}
    (word : BinaryWord total down) (length : ℕ) : ℕ :=
  (word.1.filter fun position => position.1 < length).card

def IsBallot {total down : ℕ} (word : BinaryWord total down) : Prop :=
  ∀ length ≤ total,
    prefixMinority word length ≤ length - prefixMinority word length

instance {total down : ℕ} (word : BinaryWord total down) :
    Decidable (IsBallot word) := by
  unfold IsBallot
  infer_instance

abbrev BallotWord (total down : ℕ) :=
  {word : BinaryWord total down // IsBallot word}

abbrev NegativeSectorWords (x y z : ℕ) :=
  BallotWord (2 * x + y + 2) x ×
  BallotWord (2 * y + z + 2) y ×
  BallotWord (2 * z + x + 2) z

end BenzelProblem6Kernel
