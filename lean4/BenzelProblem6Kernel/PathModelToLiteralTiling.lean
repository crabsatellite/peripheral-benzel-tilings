import BenzelProblem6Kernel.NegativeReconstructedExactCover

/-!
# Premise-free inverse from the counted path model to literal tilings
-/

namespace BenzelProblem6Kernel

noncomputable def pathModelToLiteralTiling {m : ℕ}
    (configuration : PathModelConfiguration m) : LiteralTiling m := by
  rcases configuration with ⟨sink, arms⟩
  rcases arms with positive | negative
  · exact _root_.cast (congrArg LiteralTiling sink.sum_eq)
      (positiveYLiteralTiling sink.u sink.v sink.w positive)
  · exact _root_.cast (congrArg LiteralTiling sink.sum_eq)
      (negativeYLiteralTiling sink.u sink.v sink.w negative)

theorem nonempty_literalTiling_of_pathModelConfiguration {m : ℕ}
    (configuration : PathModelConfiguration m) : Nonempty (LiteralTiling m) :=
  ⟨pathModelToLiteralTiling configuration⟩

end BenzelProblem6Kernel
