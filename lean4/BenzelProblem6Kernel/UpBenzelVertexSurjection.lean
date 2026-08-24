import BenzelProblem6Kernel.UpBenzelVertexTwoExclusions

/-! # Surjectivity and equivalence for up-type benzel vertices -/

namespace BenzelProblem6Kernel

theorem upVertexParameterToAnchor_surjective (m : ℕ) :
    Function.Surjective (upVertexParameterToAnchor m) := by
  rintro ⟨anchor, label, hmem⟩
  obtain ⟨s, hphase⟩ := exists_anchor_phase_offset (m + 3) anchor
  rcases s with ⟨s, hs⟩
  have hsCases : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases hsCases with rfl | rfl | rfl
  · obtain ⟨p, hp⟩ :=
      upAnchor_has_simplex_at_phase m 0 anchor label hmem (by
        simpa using hphase)
    refine ⟨Sum.inl p, ?_⟩
    exact Subtype.ext hp
  · obtain ⟨p, hp⟩ :=
      upAnchor_has_simplex_at_phase m 1 anchor label hmem (by
        simpa using hphase)
    have hallowed : p ∉ upOneExceptions (m + 3) :=
      upOne_simplex_allowed_of_anchor_mem m p ⟨label, by
        rwa [hp]⟩
    refine ⟨Sum.inr (Sum.inl ⟨p, hallowed⟩), ?_⟩
    exact Subtype.ext hp
  · obtain ⟨p, hp⟩ :=
      upAnchor_has_simplex_at_phase m 2 anchor label hmem (by
        simpa using hphase)
    have hallowed : p ∉ upTwoExceptions (m + 3) :=
      upTwo_simplex_allowed_of_anchor_mem m p ⟨label, by
        rwa [hp]⟩
    refine ⟨Sum.inr (Sum.inr ⟨p, hallowed⟩), ?_⟩
    exact Subtype.ext hp

noncomputable def upVertexParameterEquiv (m : ℕ) :
    UpVertexParameter (m + 3) ≃ UpBenzelVertexAnchor m :=
  Equiv.ofBijective (upVertexParameterToAnchor m)
    ⟨upVertexParameterToAnchor_injective m,
      upVertexParameterToAnchor_surjective m⟩

noncomputable instance upBenzelVertexAnchorFintype (m : ℕ) :
    Fintype (UpBenzelVertexAnchor m) :=
  Fintype.ofEquiv (UpVertexParameter (m + 3))
    (upVertexParameterEquiv m)

theorem card_upBenzelVertexAnchor (m : ℕ) :
    Fintype.card (UpBenzelVertexAnchor m) =
      (m + 5).choose 2 + ((m + 6).choose 2 - 3) +
        ((m + 7).choose 2 - 6) := by
  rw [← Fintype.card_congr (upVertexParameterEquiv m),
    card_upVertexParameter]

end BenzelProblem6Kernel
