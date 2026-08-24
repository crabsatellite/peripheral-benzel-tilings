import BenzelProblem6Kernel.LiteralTilingRoundTrip
import BenzelProblem6Kernel.MainTheoremConsumer

/-!
# The literal tiling/path-model equivalence
-/

namespace BenzelProblem6Kernel

noncomputable def literalTilingPathModelEquiv
    (hstone : conwayLagariasStoneCountTarget) (m : ℕ) :
    LiteralTiling m ≃ PathModelConfiguration m where
  toFun := literalTilingToPathModel hstone
  invFun := pathModelToLiteralTiling
  left_inv := pathModelToLiteralTiling_literalTilingToPathModel hstone
  right_inv := literalTilingToPathModel_pathModelToLiteralTiling hstone

theorem literalTilingPathModelEquivTarget_of_conwayLagarias
    (hstone : conwayLagariasStoneCountTarget) :
    literalTilingPathModelEquivTarget := by
  intro m
  exact ⟨literalTilingPathModelEquiv hstone m⟩

theorem manuscript_main_theorem_of_conwayLagarias
    (hstone : conwayLagariasStoneCountTarget)
    {n : ℕ} (hn : 5 ≤ n) :
    (type103TilingCount n : ℚ) =
      ((3 * n + 3 : ℕ) : ℚ) * factorialQ (3 * n - 7) /
        (factorialQ (n - 5) * factorialQ (2 * n - 1)) :=
  manuscript_main_theorem_of_equiv
    (literalTilingPathModelEquivTarget_of_conwayLagarias hstone) hn

end BenzelProblem6Kernel
