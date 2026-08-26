import FiniteDefects.D4ReverseBone

/-! # Source and target incidence along one abstract reverse path -/

namespace FiniteDefects

theorem reversePath_target_exists_of_ne_core {m : ℕ}
    {label : MicroLabel} {terminal core p : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges)
    (hvisit : D4AbstractPathVisits terminal core edges p)
    (hne : p ≠ core) :
    ∃ edge ∈ edges, edge.target = p ∧ edge.boneClass.label = label := by
  induction edges generalizing terminal p with
  | nil =>
      simp only [IsD4AbstractReversePath] at hpath
      rcases hvisit with hpterm | hpcore | ⟨edge, hmem, _⟩
      · subst p
        exact (hne hpath).elim
      · exact (hne hpcore).elim
      · simp at hmem
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      rcases hvisit with hpterm | hpcore | ⟨edge, hmem, hp⟩
      · subst p
        exact ⟨head, by simp, hpath.1, hpath.2.1⟩
      · exact (hne hpcore).elim
      · simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · rcases hp with hpsource | hptarget
          · subst p
            obtain ⟨candidate, hcand, htarget, hlabel⟩ :=
              ih hpath.2.2 (Or.inl rfl) hne
            exact ⟨candidate, by simp [hcand], htarget, hlabel⟩
          · subst p
            exact ⟨edge, by simp, rfl, hpath.2.1⟩
        · obtain ⟨candidate, hcand, htarget, hlabel⟩ :=
            ih hpath.2.2 (Or.inr (Or.inr ⟨edge, hmem, hp⟩)) hne
          exact ⟨candidate, by simp [hcand], htarget, hlabel⟩

theorem reversePath_source_exists_of_ne_terminal {m : ℕ}
    {label : MicroLabel} {terminal core p : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges)
    (hvisit : D4AbstractPathVisits terminal core edges p)
    (hne : p ≠ terminal) :
    ∃ edge ∈ edges, edge.source = p ∧ edge.boneClass.label = label := by
  induction edges generalizing terminal p with
  | nil =>
      simp only [IsD4AbstractReversePath] at hpath
      rcases hvisit with hpterm | hpcore | ⟨edge, hmem, _⟩
      · exact (hne hpterm).elim
      · subst p
        exact (hne hpath.symm).elim
      · simp at hmem
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      rcases hvisit with hpterm | hpcore | ⟨edge, hmem, hp⟩
      · exact (hne hpterm).elim
      · subst p
        by_cases hsource : head.source = core
        · exact ⟨head, by simp, hsource, hpath.2.1⟩
        · have hcoreVisit : D4AbstractPathVisits head.source core rest core :=
            Or.inr (Or.inl rfl)
          obtain ⟨candidate, hcand, hedge, hlabel⟩ :=
            ih hpath.2.2 hcoreVisit (by
              intro h
              exact hsource h.symm)
          exact ⟨candidate, by simp [hcand], hedge, hlabel⟩
      · simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · rcases hp with hpsource | hptarget
          · exact ⟨edge, by simp, hpsource.symm, hpath.2.1⟩
          · subst p
            exact (hne hpath.1).elim
        · by_cases hpSource : p = head.source
          · subst p
            exact ⟨head, by simp, rfl, hpath.2.1⟩
          · obtain ⟨edge', hmem', hedge', hlabel'⟩ := ih hpath.2.2
              (Or.inr (Or.inr ⟨edge, hmem, hp⟩)) (by
                intro heq
                exact hpSource heq)
            exact ⟨edge', by simp [hmem'], hedge', hlabel'⟩

end FiniteDefects
