import FiniteDefects.D4BallotFormula

/-! # Exact public interface for the all-m d=4 ballot formula -/

namespace FiniteDefects

structure D4BallotSumEvidence : Prop where
  exact_count : ∀ m : ℕ,
    d4TilingCount m = d4A m + d4C m + 3 * d4H m
  ballot_zero : ∀ x : ℕ, d4R x 0 = 1
  ballot_succ : ∀ x y : ℕ,
    d4R x (y + 1) =
      (x + 2 * (y + 1)).choose (y + 1) -
        (x + 2 * (y + 1)).choose y

end FiniteDefects
