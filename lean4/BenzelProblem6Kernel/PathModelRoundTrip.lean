import BenzelProblem6Kernel.NegativeRoundTrip

/-!
# The forward extraction is a right inverse of literal reconstruction
-/

namespace BenzelProblem6Kernel

theorem literalTilingToPathModel_pathModelToLiteralTiling
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (configuration : PathModelConfiguration m) :
    literalTilingToPathModel hstone
      (pathModelToLiteralTiling configuration) = configuration := by
  rcases configuration with ⟨sink, arms⟩
  rcases sink with ⟨x, y, z, hsum⟩
  change x + y + z = m at hsum
  subst m
  rcases arms with positive | negative
  · simpa [pathModelToLiteralTiling, reducedXYZSink] using
      literalTilingToPathModel_positive_roundTrip hstone x y z positive
  · simpa [pathModelToLiteralTiling, reducedXYZSink] using
      literalTilingToPathModel_negative_roundTrip hstone x y z negative

theorem literalTilingToPathModel_surjective
    (hstone : conwayLagariasStoneCountTarget) (m : ℕ) :
    Function.Surjective
      (literalTilingToPathModel hstone : LiteralTiling m →
        PathModelConfiguration m) := by
  intro configuration
  exact ⟨pathModelToLiteralTiling configuration,
    literalTilingToPathModel_pathModelToLiteralTiling hstone configuration⟩

end BenzelProblem6Kernel
