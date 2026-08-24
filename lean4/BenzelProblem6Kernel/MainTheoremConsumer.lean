import BenzelProblem6Kernel.ManuscriptClosedForm
import BenzelProblem6Kernel.LiteralTilingCarrier

/-!
# Fail-closed consumer for the manuscript main theorem

The path-model enumeration is now premise-free.  This file exposes the exact
remaining source bridge as a proposition and proves that consuming it yields
the displayed theorem without any further enumeration input.
-/

namespace BenzelProblem6Kernel

def literalTilingPathModelEquivTarget : Prop :=
  ∀ m : ℕ, Nonempty (LiteralTiling m ≃ PathModelConfiguration m)

theorem type103_count_eq_pathModelCount_of_equiv
    (hbridge : literalTilingPathModelEquivTarget) (m : ℕ) :
    type103TilingCount (m + 5) = pathModelCount m := by
  rw [type103TilingCount_add_five]
  obtain ⟨equiv⟩ := hbridge m
  rw [Fintype.card_congr equiv, card_pathModelConfiguration]

theorem manuscript_main_theorem_of_equiv
    (hbridge : literalTilingPathModelEquivTarget)
    {n : ℕ} (hn : 5 ≤ n) :
    (type103TilingCount n : ℚ) =
      ((3 * n + 3 : ℕ) : ℚ) * factorialQ (3 * n - 7) /
        (factorialQ (n - 5) * factorialQ (2 * n - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 5 + m = m + 5 by omega,
    type103_count_eq_pathModelCount_of_equiv hbridge m]
  exact pathModelCount_manuscript_form (n := m + 5) (by omega)

end BenzelProblem6Kernel
