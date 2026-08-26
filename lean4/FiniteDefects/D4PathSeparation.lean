import FiniteDefects.D4PathData

/-! # Automatic coordinate separation of the three abstract paths -/

namespace FiniteDefects

def D4AbstractPathVisits {m : ℕ} (terminal core : SimplexPoint (m + 2))
    (edges : List (D4LiteralDirectedEdge m))
    (p : SimplexPoint (m + 2)) : Prop :=
  p = terminal ∨ p = core ∨
    ∃ edge ∈ edges, p = edge.source ∨ p = edge.target

theorem d4AbstractEdge_zero_mono {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .zero) :
    edge.source.w ≤ edge.target.w ∧ edge.target.v ≤ edge.source.v := by
  have hallowed := goodBoneClass_step_allowed edge.boneClass
  rcases d4LiteralDirectedEdge_simplex_step edge with hA | hB | hC
  · omega
  · simp [hlabel, hB.1, allowedStep, stepA, stepB, stepC] at hallowed
  · omega

theorem d4AbstractEdge_one_mono {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .one) :
    edge.source.u ≤ edge.target.u ∧ edge.target.w ≤ edge.source.w := by
  have hallowed := goodBoneClass_step_allowed edge.boneClass
  rcases d4LiteralDirectedEdge_simplex_step edge with hA | hB | hC
  · simp [hlabel, hA.1, allowedStep, stepA, stepB, stepC] at hallowed
  · omega
  · omega

theorem d4AbstractEdge_two_mono {m : ℕ}
    (edge : D4LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .two) :
    edge.target.u ≤ edge.source.u ∧ edge.source.v ≤ edge.target.v := by
  have hallowed := goodBoneClass_step_allowed edge.boneClass
  rcases d4LiteralDirectedEdge_simplex_step edge with hA | hB | hC
  · omega
  · omega
  · simp [hlabel, hC.1, allowedStep, stepA, stepB, stepC] at hallowed

theorem d4_zero_path_bounds {m : ℕ}
    {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath .zero terminal core edges) :
    ∀ p, D4AbstractPathVisits terminal core edges p →
      core.w ≤ p.w ∧ p.v ≤ core.v := by
  induction edges generalizing terminal with
  | nil =>
      intro p hvisit
      simp only [IsD4AbstractReversePath] at hpath
      simp [D4AbstractPathVisits, hpath] at hvisit
      rcases hvisit with rfl | rfl
      all_goals omega
  | cons edge rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      have hrest := ih hpath.2.2
      have hsource := hrest edge.source (Or.inl rfl)
      have hmono := d4AbstractEdge_zero_mono edge hpath.2.1
      intro p hvisit
      rcases hvisit with rfl | rfl | ⟨candidate, hmem, hp⟩
      · rw [← hpath.1]
        omega
      · omega
      · simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · rcases hp with rfl | rfl <;> omega
        · exact hrest p (Or.inr (Or.inr ⟨candidate, hmem, hp⟩))

theorem d4_one_path_bounds {m : ℕ}
    {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath .one terminal core edges) :
    ∀ p, D4AbstractPathVisits terminal core edges p →
      core.u ≤ p.u ∧ p.w ≤ core.w := by
  induction edges generalizing terminal with
  | nil =>
      intro p hvisit
      simp only [IsD4AbstractReversePath] at hpath
      simp [D4AbstractPathVisits, hpath] at hvisit
      rcases hvisit with rfl | rfl
      all_goals omega
  | cons edge rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      have hrest := ih hpath.2.2
      have hsource := hrest edge.source (Or.inl rfl)
      have hmono := d4AbstractEdge_one_mono edge hpath.2.1
      intro p hvisit
      rcases hvisit with rfl | rfl | ⟨candidate, hmem, hp⟩
      · rw [← hpath.1]
        omega
      · omega
      · simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · rcases hp with rfl | rfl <;> omega
        · exact hrest p (Or.inr (Or.inr ⟨candidate, hmem, hp⟩))

theorem d4_two_path_bounds {m : ℕ}
    {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath .two terminal core edges) :
    ∀ p, D4AbstractPathVisits terminal core edges p →
      p.u ≤ core.u ∧ core.v ≤ p.v := by
  induction edges generalizing terminal with
  | nil =>
      intro p hvisit
      simp only [IsD4AbstractReversePath] at hpath
      simp [D4AbstractPathVisits, hpath] at hvisit
      rcases hvisit with rfl | rfl
      all_goals omega
  | cons edge rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      have hrest := ih hpath.2.2
      have hsource := hrest edge.source (Or.inl rfl)
      have hmono := d4AbstractEdge_two_mono edge hpath.2.1
      intro p hvisit
      rcases hvisit with rfl | rfl | ⟨candidate, hmem, hp⟩
      · rw [← hpath.1]
        omega
      · omega
      · simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · rcases hp with rfl | rfl <;> omega
        · exact hrest p (Or.inr (Or.inr ⟨candidate, hmem, hp⟩))

theorem d4_paths_zero_one_disjoint {m : ℕ} (data : D4DefectPathData m)
    (p : SimplexPoint (m + 2))
    (hzero : D4AbstractPathVisits (d4BoundaryOwner m .zero)
      (data.defect.core .zero) (data.paths .zero) p)
    (hone : D4AbstractPathVisits (d4BoundaryOwner m .one)
      (data.defect.core .one) (data.paths .one) p) : False := by
  have hz := d4_zero_path_bounds (data.path_spec .zero) p hzero
  have ho := d4_one_path_bounds (data.path_spec .one) p hone
  have hsep := data.defect.core_zero_w_gt_one
  omega

theorem d4_paths_one_two_disjoint {m : ℕ} (data : D4DefectPathData m)
    (p : SimplexPoint (m + 2))
    (hone : D4AbstractPathVisits (d4BoundaryOwner m .one)
      (data.defect.core .one) (data.paths .one) p)
    (htwo : D4AbstractPathVisits (d4BoundaryOwner m .two)
      (data.defect.core .two) (data.paths .two) p) : False := by
  have ho := d4_one_path_bounds (data.path_spec .one) p hone
  have ht := d4_two_path_bounds (data.path_spec .two) p htwo
  have hsep := data.defect.core_one_u_gt_two
  omega

theorem d4_paths_two_zero_disjoint {m : ℕ} (data : D4DefectPathData m)
    (p : SimplexPoint (m + 2))
    (htwo : D4AbstractPathVisits (d4BoundaryOwner m .two)
      (data.defect.core .two) (data.paths .two) p)
    (hzero : D4AbstractPathVisits (d4BoundaryOwner m .zero)
      (data.defect.core .zero) (data.paths .zero) p) : False := by
  have ht := d4_two_path_bounds (data.path_spec .two) p htwo
  have hz := d4_zero_path_bounds (data.path_spec .zero) p hzero
  have hsep := data.defect.core_two_v_gt_zero
  omega

end FiniteDefects
