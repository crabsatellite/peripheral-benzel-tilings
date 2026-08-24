import BenzelProblem6Kernel.DownBenzelVertexPhaseShift

/-! # Surjectivity and equivalence for down-type benzel vertices -/

namespace BenzelProblem6Kernel

theorem downVertexParameterToAnchor_surjective (m : ℕ) :
    Function.Surjective (downVertexParameterToAnchor m) := by
  rintro ⟨anchor, label, hmem⟩
  obtain ⟨s, hphase⟩ := exists_anchor_phase_offset (m + 3) anchor
  rcases s with ⟨s, hs⟩
  have hsCases : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases hsCases with rfl | rfl | rfl
  · obtain ⟨p, hp⟩ :=
      downZero_anchor_has_parameter m anchor label hmem (by
        simpa using hphase)
    have hallowed : p ∉ downZeroExceptions (m + 3) := by
      intro hexception
      simp only [downZeroExceptions, Finset.mem_insert,
        Finset.mem_singleton] at hexception
      rcases hexception with hpoint | hpoint
      · subst p
        rw [← hp] at hmem
        cases label <;>
          simp [downZeroSimplexAnchor, downAnchorCell,
            inPeripheralBenzel, sourceZero] at hmem <;> omega
      · subst p
        rw [← hp] at hmem
        cases label <;>
          simp [downZeroSimplexAnchor, downAnchorCell,
            inPeripheralBenzel, sourceOne] at hmem <;> omega
    refine ⟨Sum.inl ⟨p, hallowed⟩, ?_⟩
    exact Subtype.ext hp
  · obtain ⟨p, hp⟩ :=
      downOne_anchor_has_parameter m anchor label hmem (by
        simpa using hphase)
    have hallowed : p ∉ downOneExceptions (m + 3) :=
      downOne_simplex_allowed_of_anchor_mem m p ⟨label, by
        rw [downOneSimplexAnchor] at hp
        rw [hp]
        exact hmem⟩
    refine ⟨Sum.inr (Sum.inl ⟨p, hallowed⟩), ?_⟩
    exact Subtype.ext hp
  · obtain ⟨p, hp⟩ :=
      downTwo_anchor_has_parameter m anchor label hmem (by
        simpa using hphase)
    have hallowed : p ∉ downTwoExceptions (m + 3) := by
      intro hexception
      simp only [downTwoExceptions, Finset.mem_insert,
        Finset.mem_singleton] at hexception
      rcases hexception with hpoint | hpoint
      · subst p
        rw [← hp] at hmem
        cases label <;>
          simp [downTwoSimplexAnchor, downAnchorCell,
            inPeripheralBenzel, sourceOne] at hmem <;> omega
      · subst p
        rw [← hp] at hmem
        cases label <;>
          simp [downTwoSimplexAnchor, downAnchorCell,
            inPeripheralBenzel, sourceTwo] at hmem <;> omega
    refine ⟨Sum.inr (Sum.inr ⟨p, hallowed⟩), ?_⟩
    exact Subtype.ext hp

noncomputable def downVertexParameterEquiv (m : ℕ) :
    DownVertexParameter (m + 3) ≃ DownBenzelVertexAnchor m :=
  Equiv.ofBijective (downVertexParameterToAnchor m)
    ⟨downVertexParameterToAnchor_injective m,
      downVertexParameterToAnchor_surjective m⟩

noncomputable instance downBenzelVertexAnchorFintype (m : ℕ) :
    Fintype (DownBenzelVertexAnchor m) :=
  Fintype.ofEquiv (DownVertexParameter (m + 3))
    (downVertexParameterEquiv m)

theorem card_downBenzelVertexAnchor (m : ℕ) :
    Fintype.card (DownBenzelVertexAnchor m) =
      3 * ((m + 6).choose 2 - 2) := by
  rw [← Fintype.card_congr (downVertexParameterEquiv m),
    card_downVertexParameter]

end BenzelProblem6Kernel
