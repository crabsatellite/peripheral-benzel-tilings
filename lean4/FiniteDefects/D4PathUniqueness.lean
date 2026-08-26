import FiniteDefects.D4Reconstruction

/-! # Rank uniqueness of source and target vertices within one path -/

namespace FiniteDefects

theorem d4AbstractEdge_rank_step {m : ℕ} (edge : D4LiteralDirectedEdge m) :
    d4LabelRank edge.boneClass.label edge.target =
      d4LabelRank edge.boneClass.label edge.source + 1 := by
  have hallowed := goodBoneClass_step_allowed edge.boneClass
  have hanchor := d4LiteralDirectedEdge_anchor_step edge
  have hpotential := allowedStep_potential_increase edge.boneClass.label
    (ownerQ edge.source) (ownerR edge.source)
    edge.boneClass.step.1 edge.boneClass.step.2 hallowed
  have hq := congrArg Prod.fst hanchor
  have hr := congrArg Prod.snd hanchor
  simp only [addCell] at hq hr
  have hinc : ownerPotential edge.boneClass.label
      (ownerQ edge.target) (ownerR edge.target) =
      ownerPotential edge.boneClass.label
        (ownerQ edge.source) (ownerR edge.source) + 1 := by
    rw [← hq, ← hr]
    exact hpotential
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [d4LabelRank_cast, d4LabelRank_cast]
  omega

theorem reversePath_source_rank_lt_terminal {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges) :
    ∀ edge ∈ edges,
      d4LabelRank label edge.source < d4LabelRank label terminal := by
  induction edges generalizing terminal with
  | nil => simp
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      have hheadStep := d4AbstractEdge_rank_step head
      rw [hpath.2.1] at hheadStep
      intro edge hedge
      simp only [List.mem_cons] at hedge
      rcases hedge with rfl | hedge
      · rw [← hpath.1, hheadStep]
        omega
      · have htail := ih hpath.2.2 edge hedge
        rw [← hpath.1, hheadStep]
        omega

theorem reversePath_target_rank_le_terminal {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges) :
    ∀ edge ∈ edges,
      d4LabelRank label edge.target ≤ d4LabelRank label terminal := by
  induction edges generalizing terminal with
  | nil => simp
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      intro edge hedge
      simp only [List.mem_cons] at hedge
      rcases hedge with rfl | hedge
      · rw [hpath.1]
      · have htail := ih hpath.2.2 edge hedge
        have hheadStep := d4AbstractEdge_rank_step head
        rw [hpath.2.1] at hheadStep
        rw [← hpath.1, hheadStep]
        omega

theorem reversePath_source_unique {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges)
    (left right : D4LiteralDirectedEdge m)
    (hleft : left ∈ edges) (hright : right ∈ edges)
    (hsource : left.source = right.source) : left = right := by
  induction edges generalizing terminal with
  | nil => simp at hleft
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · have hrank := reversePath_source_rank_lt_terminal hpath.2.2 right hright
        rw [← hsource] at hrank
        exact (Nat.lt_irrefl _ hrank).elim
      · have hrank := reversePath_source_rank_lt_terminal hpath.2.2 left hleft
        rw [hsource] at hrank
        exact (Nat.lt_irrefl _ hrank).elim
      · exact ih hpath.2.2 hleft hright

theorem reversePath_target_unique {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges)
    (left right : D4LiteralDirectedEdge m)
    (hleft : left ∈ edges) (hright : right ∈ edges)
    (htarget : left.target = right.target) : left = right := by
  induction edges generalizing terminal with
  | nil => simp at hleft
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · have hrank := reversePath_target_rank_le_terminal hpath.2.2 right hright
        have hheadStep := d4AbstractEdge_rank_step left
        rw [hpath.2.1] at hheadStep
        rw [← htarget, hheadStep] at hrank
        omega
      · have hrank := reversePath_target_rank_le_terminal hpath.2.2 left hleft
        have hheadStep := d4AbstractEdge_rank_step right
        rw [hpath.2.1] at hheadStep
        rw [htarget, hheadStep] at hrank
        omega
      · exact ih hpath.2.2 hleft hright

theorem reversePath_core_rank_le_terminal {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges) :
    d4LabelRank label core ≤ d4LabelRank label terminal := by
  induction edges generalizing terminal with
  | nil =>
      simp only [IsD4AbstractReversePath] at hpath
      rw [hpath]
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      have htail := ih hpath.2.2
      have hstep := d4AbstractEdge_rank_step head
      rw [hpath.2.1] at hstep
      rw [← hpath.1, hstep]
      omega

theorem reversePath_core_rank_le_source {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges) :
    ∀ edge ∈ edges,
      d4LabelRank label core ≤ d4LabelRank label edge.source := by
  induction edges generalizing terminal with
  | nil => simp
  | cons head rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      intro edge hedge
      simp only [List.mem_cons] at hedge
      rcases hedge with rfl | hedge
      · exact reversePath_core_rank_le_terminal hpath.2.2
      · exact ih hpath.2.2 edge hedge

theorem reversePath_target_ne_core {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ edges) :
    edge.target ≠ core := by
  intro heq
  have hsource := reversePath_core_rank_le_source hpath edge hmem
  have hstep := d4AbstractEdge_rank_step edge
  rw [(hpath.all_labels edge hmem), heq] at hstep
  omega

end FiniteDefects
