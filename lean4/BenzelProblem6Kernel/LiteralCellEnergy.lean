import BenzelProblem6Kernel.OwnerRegionEnergy
import BenzelProblem6Kernel.BenzelArea
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Literal cell energy and the owner-side region sum

This file assigns to each literal benzel cell the energy of its unique
periodic owner.  It then reindexes the cell sum through the literal
cell--owner equivalence and proves that the result is the already checked
simplex-owner energy sum.
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

noncomputable def literalCellEnergy {n : ℕ} (hn : 5 ≤ n)
    (cell : BenzelCell n) : ℤ :=
  ownerLabelEnergy (chosenOwnerPair hn cell).1.1
    (chosenOwnerPair hn cell).1.2

theorem ownerPresentEnergy_eq_label_sum {n : ℕ}
    (p : SimplexPoint (n - 2)) :
    ownerPresentEnergy p =
      ∑ label : MicroLabel,
        if IsPresentOwnerLabel n (p, label) then
          ownerLabelEnergy p label else 0 := by
  change ownerPresentEnergy p =
    ∑ label : MicroLabel,
      if inPeripheralBenzel n (ownerCell p label) then
        ownerLabelEnergy p label else 0
  have huniv : (Finset.univ : Finset MicroLabel) =
      {.zero, .one, .two} := by
    ext label
    rcases label with _ | _ | _ <;> simp
  rw [show (∑ label : MicroLabel,
      if inPeripheralBenzel n (ownerCell p label) then
        ownerLabelEnergy p label else 0) =
      ∑ label ∈ (Finset.univ : Finset MicroLabel),
        if inPeripheralBenzel n (ownerCell p label) then
          ownerLabelEnergy p label else 0 by simp]
  rw [huniv]
  simp [ownerPresentEnergy]
  ring_nf

theorem present_owner_label_energy_sum {n : ℕ} :
    ∑ pair : PresentOwnerLabel n,
        ownerLabelEnergy pair.1.1 pair.1.2 =
      ∑ p : SimplexPoint (n - 2), ownerPresentEnergy p := by
  classical
  calc
    (∑ pair : PresentOwnerLabel n,
        ownerLabelEnergy pair.1.1 pair.1.2) =
        ∑ pair : OwnerLabelPair n,
          if IsPresentOwnerLabel n pair then
            ownerLabelEnergy pair.1 pair.2 else 0 := by
      symm
      calc
        (∑ pair : OwnerLabelPair n,
            if IsPresentOwnerLabel n pair then
              ownerLabelEnergy pair.1 pair.2 else 0) =
            ∑ pair ∈ Finset.univ.filter (IsPresentOwnerLabel n),
              ownerLabelEnergy pair.1 pair.2 := by
          rw [Finset.sum_filter]
        _ = ∑ pair : PresentOwnerLabel n,
              ownerLabelEnergy pair.1.1 pair.1.2 := by
          apply Finset.sum_subtype
          intro pair
          simp
    _ = ∑ p : SimplexPoint (n - 2),
          ∑ label : MicroLabel,
            if IsPresentOwnerLabel n (p, label) then
              ownerLabelEnergy p label else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p : SimplexPoint (n - 2), ownerPresentEnergy p := by
      apply Finset.sum_congr rfl
      intro p _
      exact (ownerPresentEnergy_eq_label_sum p).symm

theorem literal_cell_energy_sum {n : ℕ} (hn : 5 ≤ n) :
    letI := benzelCellFintypeOf hn
    ∑ cell : BenzelCell n, literalCellEnergy hn cell =
      3 * ((n - 2 : ℕ) : ℤ) := by
  letI := benzelCellFintypeOf hn
  calc
    (∑ cell : BenzelCell n, literalCellEnergy hn cell) =
        ∑ pair : PresentOwnerLabel n,
          ownerLabelEnergy pair.1.1 pair.1.2 := by
      apply Fintype.sum_equiv (benzelOwnerEquiv hn)
      intro cell
      rfl
    _ = ∑ p : SimplexPoint (n - 2), ownerPresentEnergy p :=
      present_owner_label_energy_sum
    _ = 3 * ((n - 2 : ℕ) : ℤ) := total_owner_present_energy hn

end BenzelProblem6Kernel
