import D4KernelOnly.D4CellVertexCarrier

/-! # The three up-anchor difference from the adjacent wide benzel -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 1000000

noncomputable def p6UpAnchorValueFinset (m : ℕ) : Finset Cell :=
  (Finset.univ : Finset (UpBenzelVertexAnchor m)).image Subtype.val

def d4RemovedUpAnchors (m : ℕ) : Finset Cell :=
  {(-((m : ℤ)) - 4, (m : ℤ) + 3),
    (1, -((m : ℤ)) - 4),
    ((m : ℤ) + 3, 1)}

theorem mem_p6UpAnchorValueFinset_iff (m : ℕ) (anchor : Cell) :
    anchor ∈ p6UpAnchorValueFinset m ↔
      ∃ label : BenzelProblem6Kernel.MicroLabel,
        inPeripheralBenzel (m + 5)
          (BenzelProblem6Kernel.cellForOwnerAnchor anchor label) := by
  simp [p6UpAnchorValueFinset, UpBenzelVertexAnchor]

theorem d4WideUp_not_d4_iff (m : ℕ) (anchor : Cell) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
        inPeripheralBenzel (m + 5)
          (BenzelProblem6Kernel.cellForOwnerAnchor anchor label)) ∧
      ¬(∃ label : BenzelProblem6Kernel.MicroLabel,
        inBenzel (m + 5) (2 * m + 6)
          (BenzelProblem6Kernel.cellForOwnerAnchor anchor label)) ↔
    anchor = (-((m : ℤ)) - 4, (m : ℤ) + 3) ∨
      anchor = (1, -((m : ℤ)) - 4) ∨
      anchor = ((m : ℤ) + 3, 1) := by
  rcases anchor with ⟨i, j⟩
  constructor
  · rintro ⟨⟨label, hwide⟩, hnarrow⟩
    have hzero : ¬inBenzel (m + 5) (2 * m + 6)
        (BenzelProblem6Kernel.cellForOwnerAnchor (i, j) .zero) :=
      fun h => hnarrow ⟨.zero, h⟩
    have hone : ¬inBenzel (m + 5) (2 * m + 6)
        (BenzelProblem6Kernel.cellForOwnerAnchor (i, j) .one) :=
      fun h => hnarrow ⟨.one, h⟩
    have htwo : ¬inBenzel (m + 5) (2 * m + 6)
        (BenzelProblem6Kernel.cellForOwnerAnchor (i, j) .two) :=
      fun h => hnarrow ⟨.two, h⟩
    cases label
    all_goals
      simp [inPeripheralBenzel, inBenzel,
        BenzelProblem6Kernel.cellForOwnerAnchor] at hwide hzero hone htwo ⊢
    all_goals omega
  · intro hanchor
    rcases hanchor with hanchor | hanchor | hanchor
    · injection hanchor with hi hj
      subst i; subst j
      constructor
      · exact ⟨.one, by
          simp [inPeripheralBenzel,
            BenzelProblem6Kernel.cellForOwnerAnchor]
          omega⟩
      · rintro ⟨label, hcell⟩
        cases label <;>
          simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor] at hcell <;>
          omega
    · injection hanchor with hi hj
      subst i; subst j
      constructor
      · exact ⟨.two, by
          simp [inPeripheralBenzel,
            BenzelProblem6Kernel.cellForOwnerAnchor]
          omega⟩
      · rintro ⟨label, hcell⟩
        cases label <;>
          simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor] at hcell <;>
          omega
    · injection hanchor with hi hj
      subst i; subst j
      constructor
      · exact ⟨.zero, by
          simp [inPeripheralBenzel,
            BenzelProblem6Kernel.cellForOwnerAnchor]
          omega⟩
      · rintro ⟨label, hcell⟩
        cases label <;>
          simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor] at hcell <;>
          omega

theorem d4UpAnchor_subset_wide (m : ℕ) :
    d4UpAnchorFinset (m + 1) ⊆ p6UpAnchorValueFinset m := by
  intro anchor hanchor
  rw [mem_p6UpAnchorValueFinset_iff]
  obtain ⟨label, hcell⟩ :=
    (mem_d4UpAnchorFinset_iff (m + 1) anchor).1 hanchor
  refine ⟨label, ?_⟩
  simp [inPeripheralBenzel, inBenzel] at hcell ⊢
  omega

theorem p6Up_sdiff_d4_eq_removed (m : ℕ) :
    p6UpAnchorValueFinset m \ d4UpAnchorFinset (m + 1) =
      d4RemovedUpAnchors m := by
  ext anchor
  rw [Finset.mem_sdiff, mem_p6UpAnchorValueFinset_iff,
    mem_d4UpAnchorFinset_iff]
  simp only [show m + 1 + 4 = m + 5 by omega,
    show 2 * (m + 1) + 4 = 2 * m + 6 by omega]
  rw [d4WideUp_not_d4_iff]
  simp [d4RemovedUpAnchors]

theorem card_d4RemovedUpAnchors (m : ℕ) :
    (d4RemovedUpAnchors m).card = 3 := by
  let a : Cell := (-((m : ℤ)) - 4, (m : ℤ) + 3)
  let b : Cell := (1, -((m : ℤ)) - 4)
  let c : Cell := ((m : ℤ) + 3, 1)
  have hab : a ≠ b := by
    intro h
    have := congrArg Prod.fst h
    simp [a, b] at this
    omega
  have hac : a ≠ c := by
    intro h
    have := congrArg Prod.fst h
    simp [a, c] at this
    omega
  have hbc : b ≠ c := by
    intro h
    have := congrArg Prod.snd h
    simp [b, c] at this
    omega
  simp [d4RemovedUpAnchors, a, b, c, hab, hac, hbc,
    Ne.symm hab, Ne.symm hac, Ne.symm hbc]

theorem card_p6UpAnchorValueFinset (m : ℕ) :
    (p6UpAnchorValueFinset m).card =
      Fintype.card (UpBenzelVertexAnchor m) := by
  rw [p6UpAnchorValueFinset, Finset.card_image_iff.mpr
    Subtype.val_injective.injOn]
  change Fintype.card (UpBenzelVertexAnchor m) = _
  rfl

theorem card_d4UpAnchorFinset_succ (m : ℕ) :
    (d4UpAnchorFinset (m + 1)).card =
      Fintype.card (UpBenzelVertexAnchor m) - 3 := by
  have hcard := Finset.card_sdiff_add_card_eq_card
    (d4UpAnchor_subset_wide m)
  rw [p6Up_sdiff_d4_eq_removed, card_d4RemovedUpAnchors,
    card_p6UpAnchorValueFinset] at hcard
  omega

end FiniteDefects
