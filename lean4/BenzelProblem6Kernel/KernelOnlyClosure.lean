import BenzelProblem6Kernel.TreeContourWord
import BenzelProblem6Kernel.LiteralPathModelEquiv

/-! # Premise-free kernel-only closure of the manuscript endpoints -/

namespace BenzelProblem6Kernel

theorem rightStoneCount_proved {m : ℕ} (tiling : LiteralTiling m) :
    rightStoneCount tiling = m * (m + 3) / 2 := by
  exact rightStoneCount_of_rightmostTerminal tiling
    (literalTilingRightmostTerminal_word_empty tiling)

theorem conwayLagariasStoneCountTarget_proved :
    conwayLagariasStoneCountTarget := by
  intro m tiling
  exact rightStoneCount_proved tiling

noncomputable def literalTilingPathModelEquiv_proved (m : ℕ) :
    LiteralTiling m ≃ PathModelConfiguration m :=
  literalTilingPathModelEquiv conwayLagariasStoneCountTarget_proved m

theorem literalTilingPathModelEquivTarget_proved :
    literalTilingPathModelEquivTarget :=
  literalTilingPathModelEquivTarget_of_conwayLagarias
    conwayLagariasStoneCountTarget_proved

theorem manuscript_main_theorem_proved
    {n : ℕ} (hn : 5 ≤ n) :
    (type103TilingCount n : ℚ) =
      ((3 * n + 3 : ℕ) : ℚ) * factorialQ (3 * n - 7) /
        (factorialQ (n - 5) * factorialQ (2 * n - 1)) :=
  manuscript_main_theorem_of_conwayLagarias
    conwayLagariasStoneCountTarget_proved hn

end BenzelProblem6Kernel
