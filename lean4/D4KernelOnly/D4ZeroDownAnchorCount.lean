import D4KernelOnly.D4ZeroUpAnchorCount

/-! # The finite m=0 down-anchor base case -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false

def d4ZeroDownFirstCoordinateFinset : Finset ℤ := {-1, 0, 1, 2, 3}
def d4ZeroDownSecondCoordinateFinset : Finset ℤ := {-2, -1, 0, 1, 2}

def d4ZeroDownAnchors : Finset Cell :=
  (d4ZeroDownFirstCoordinateFinset.product
    d4ZeroDownSecondCoordinateFinset).filter fun anchor =>
      ∃ label : BenzelProblem6Kernel.MicroLabel,
        inBenzel 4 4 (downAnchorCell anchor label)

theorem d4DownAnchorFinset_zero :
    d4DownAnchorFinset 0 = d4ZeroDownAnchors := by
  ext anchor
  rw [mem_d4DownAnchorFinset_iff]
  rcases anchor with ⟨i, j⟩
  simp only [d4ZeroDownAnchors, Finset.mem_filter, Finset.mem_product]
  constructor
  · intro hcell
    refine ⟨?_, by simpa using hcell⟩
    obtain ⟨label, hlabel⟩ := hcell
    cases label <;> simp [inBenzel, downAnchorCell] at hlabel
    all_goals
      simp [d4ZeroDownFirstCoordinateFinset,
        d4ZeroDownSecondCoordinateFinset] <;> omega
  · rintro ⟨hbox, hcell⟩
    simpa using hcell

theorem card_d4DownAnchorFinset_zero :
    (d4DownAnchorFinset 0).card = 18 := by
  rw [d4DownAnchorFinset_zero]
  decide

end FiniteDefects
