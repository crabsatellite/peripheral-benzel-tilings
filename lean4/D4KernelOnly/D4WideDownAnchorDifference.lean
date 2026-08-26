import D4KernelOnly.D4WideUpAnchorDifference

/-! # The six down-anchor difference from the adjacent wide benzel -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 2000000

noncomputable def p6DownAnchorValueFinset (m : ℕ) : Finset Cell :=
  (Finset.univ : Finset (DownBenzelVertexAnchor m)).image Subtype.val

def d4RemovedDownAnchors (m : ℕ) : Finset Cell :=
  {(-((m : ℤ)) - 3, (m : ℤ) + 2),
    (-((m : ℤ)) - 3, (m : ℤ) + 3),
    (1, -((m : ℤ)) - 4),
    (2, -((m : ℤ)) - 4),
    ((m : ℤ) + 3, 1),
    ((m : ℤ) + 4, 0)}

theorem mem_p6DownAnchorValueFinset_iff (m : ℕ) (anchor : Cell) :
    anchor ∈ p6DownAnchorValueFinset m ↔
      ∃ label : BenzelProblem6Kernel.MicroLabel,
        inPeripheralBenzel (m + 5) (downAnchorCell anchor label) := by
  simp [p6DownAnchorValueFinset, DownBenzelVertexAnchor]

theorem d4WideDown_not_d4_iff (m : ℕ) (anchor : Cell) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
        inPeripheralBenzel (m + 5) (downAnchorCell anchor label)) ∧
      ¬(∃ label : BenzelProblem6Kernel.MicroLabel,
        inBenzel (m + 5) (2 * m + 6) (downAnchorCell anchor label)) ↔
    anchor = (-((m : ℤ)) - 3, (m : ℤ) + 2) ∨
      anchor = (-((m : ℤ)) - 3, (m : ℤ) + 3) ∨
      anchor = (1, -((m : ℤ)) - 4) ∨
      anchor = (2, -((m : ℤ)) - 4) ∨
      anchor = ((m : ℤ) + 3, 1) ∨
      anchor = ((m : ℤ) + 4, 0) := by
  rcases anchor with ⟨i, j⟩
  constructor
  · rintro ⟨⟨label, hwide⟩, hnarrow⟩
    have hzero : ¬inBenzel (m + 5) (2 * m + 6)
        (downAnchorCell (i, j) .zero) := fun h => hnarrow ⟨.zero, h⟩
    have hone : ¬inBenzel (m + 5) (2 * m + 6)
        (downAnchorCell (i, j) .one) := fun h => hnarrow ⟨.one, h⟩
    have htwo : ¬inBenzel (m + 5) (2 * m + 6)
        (downAnchorCell (i, j) .two) := fun h => hnarrow ⟨.two, h⟩
    cases label
    all_goals
      simp [inPeripheralBenzel, inBenzel, downAnchorCell] at hwide hzero hone htwo ⊢
    all_goals omega
  · intro hanchor
    rcases hanchor with hanchor | hanchor | hanchor | hanchor |
      hanchor | hanchor
    all_goals injection hanchor with hi hj
    all_goals subst i; subst j
    all_goals constructor
    all_goals first
      | exact ⟨.one, by simp [inPeripheralBenzel, downAnchorCell]; omega⟩
      | exact ⟨.zero, by simp [inPeripheralBenzel, downAnchorCell]; omega⟩
      | exact ⟨.two, by simp [inPeripheralBenzel, downAnchorCell]; omega⟩
      | (rintro ⟨label, hcell⟩;
          cases label <;> simp [inBenzel, downAnchorCell] at hcell <;> omega)

theorem d4DownAnchor_subset_wide (m : ℕ) :
    d4DownAnchorFinset (m + 1) ⊆ p6DownAnchorValueFinset m := by
  intro anchor hanchor
  rw [mem_p6DownAnchorValueFinset_iff]
  obtain ⟨label, hcell⟩ :=
    (mem_d4DownAnchorFinset_iff (m + 1) anchor).1 hanchor
  refine ⟨label, ?_⟩
  simp [inPeripheralBenzel, inBenzel] at hcell ⊢
  omega

theorem p6Down_sdiff_d4_eq_removed (m : ℕ) :
    p6DownAnchorValueFinset m \ d4DownAnchorFinset (m + 1) =
      d4RemovedDownAnchors m := by
  ext anchor
  rw [Finset.mem_sdiff, mem_p6DownAnchorValueFinset_iff,
    mem_d4DownAnchorFinset_iff]
  simp only [show m + 1 + 4 = m + 5 by omega,
    show 2 * (m + 1) + 4 = 2 * m + 6 by omega]
  rw [d4WideDown_not_d4_iff]
  simp [d4RemovedDownAnchors]

theorem card_d4RemovedDownAnchors (m : ℕ) :
    (d4RemovedDownAnchors m).card = 6 := by
  unfold d4RemovedDownAnchors
  rw [Finset.card_insert_of_not_mem]
  rw [Finset.card_insert_of_not_mem]
  rw [Finset.card_insert_of_not_mem]
  rw [Finset.card_insert_of_not_mem]
  rw [Finset.card_insert_of_not_mem]
  simp
  all_goals simp [Prod.ext_iff] <;> omega

theorem card_p6DownAnchorValueFinset (m : ℕ) :
    (p6DownAnchorValueFinset m).card =
      Fintype.card (DownBenzelVertexAnchor m) := by
  rw [p6DownAnchorValueFinset, Finset.card_image_iff.mpr
    Subtype.val_injective.injOn]
  change Fintype.card (DownBenzelVertexAnchor m) = _
  rfl

theorem card_d4DownAnchorFinset_succ (m : ℕ) :
    (d4DownAnchorFinset (m + 1)).card =
      Fintype.card (DownBenzelVertexAnchor m) - 6 := by
  have hcard := Finset.card_sdiff_add_card_eq_card
    (d4DownAnchor_subset_wide m)
  rw [p6Down_sdiff_d4_eq_removed, card_d4RemovedDownAnchors,
    card_p6DownAnchorValueFinset] at hcard
  omega

end FiniteDefects
