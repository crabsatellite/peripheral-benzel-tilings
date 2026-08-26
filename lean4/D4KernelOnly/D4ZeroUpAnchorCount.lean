import D4KernelOnly.D4WideAnchorDifference

/-! # The finite m=0 up-anchor base case -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

def d4ZeroCoordinateFinset : Finset ℤ := {-2, -1, 0, 1, 2}

def d4ZeroUpAnchors : Finset Cell :=
  (d4ZeroCoordinateFinset.product d4ZeroCoordinateFinset).filter
    fun anchor => ∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel 4 4
        (BenzelProblem6Kernel.cellForOwnerAnchor anchor label)

theorem d4UpAnchorFinset_zero : d4UpAnchorFinset 0 = d4ZeroUpAnchors := by
  ext anchor
  rw [mem_d4UpAnchorFinset_iff]
  rcases anchor with ⟨i, j⟩
  simp only [d4ZeroUpAnchors, Finset.mem_filter, Finset.mem_product]
  constructor
  · intro hcell
    refine ⟨?_, by simpa using hcell⟩
    obtain ⟨label, hlabel⟩ := hcell
    cases label <;>
      simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor] at hlabel
    all_goals simp [d4ZeroCoordinateFinset] <;> omega
  · rintro ⟨hbox, hcell⟩
    simpa using hcell

theorem card_d4UpAnchorFinset_zero : (d4UpAnchorFinset 0).card = 19 := by
  rw [d4UpAnchorFinset_zero]
  decide

end FiniteDefects
