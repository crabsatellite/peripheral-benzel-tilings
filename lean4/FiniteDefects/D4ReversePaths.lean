import FiniteDefects.D4Predecessor

/-! # The three canonical backward paths from boundary to defect -/

namespace FiniteDefects

def d4LabelRank {t : ℕ} : MicroLabel → SimplexPoint t → ℕ
  | .zero, p => p.u + 2 * p.w
  | .one, p => 2 * p.u + p.v
  | .two, p => 2 * p.v + p.w

theorem d4LabelRank_cast {t : ℕ} (label : MicroLabel) (p : SimplexPoint t) :
    (d4LabelRank label p : ℤ) =
      (t : ℤ) + ownerPotential label (ownerQ p) (ownerR p) := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  rcases label <;> simp [d4LabelRank, ownerPotential, ownerQ, ownerR] <;> omega

theorem d4TilingEdge_rank_step {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    d4LabelRank edge.label edge.target =
      d4LabelRank edge.label edge.source + 1 := by
  have hallowed := d4TilingEdge_label_allowed edge
  have hanchor := d4LiteralDirectedEdge_anchor_step edge.edge
  have hpotential := allowedStep_potential_increase edge.label
    (ownerQ edge.source) (ownerR edge.source) edge.step.1 edge.step.2
    hallowed
  have hq := congrArg Prod.fst hanchor
  have hr := congrArg Prod.snd hanchor
  simp only [addCell] at hq hr
  change ownerQ edge.source + edge.step.1 = ownerQ edge.target at hq
  change ownerR edge.source + edge.step.2 = ownerR edge.target at hr
  have hinc :
      ownerPotential edge.label (ownerQ edge.target) (ownerR edge.target) =
        ownerPotential edge.label (ownerQ edge.source) (ownerR edge.source) + 1 := by
    rw [← hq, ← hr]
    exact hpotential
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [d4LabelRank_cast, d4LabelRank_cast]
  omega

noncomputable def d4PreviousEdge {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotcore : edge.source ≠ d4DefectCore tiling edge.label) :
    D4GoodBonePlacement tiling :=
  (d4_edge_source_predecessor edge hnotcore).choose

theorem d4PreviousEdge_target {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotcore : edge.source ≠ d4DefectCore tiling edge.label) :
    (d4PreviousEdge edge hnotcore).target = edge.source :=
  (d4_edge_source_predecessor edge hnotcore).choose_spec.1.1

theorem d4PreviousEdge_label {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotcore : edge.source ≠ d4DefectCore tiling edge.label) :
    (d4PreviousEdge edge hnotcore).label = edge.label :=
  (d4_edge_source_predecessor edge hnotcore).choose_spec.1.2

theorem d4PreviousEdge_rank_lt {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotcore : edge.source ≠ d4DefectCore tiling edge.label) :
    d4LabelRank (d4PreviousEdge edge hnotcore).label
        (d4PreviousEdge edge hnotcore).source <
      d4LabelRank edge.label edge.source := by
  have hstep := d4TilingEdge_rank_step (d4PreviousEdge edge hnotcore)
  rw [d4PreviousEdge_target edge hnotcore] at hstep
  have hlabel := d4PreviousEdge_label edge hnotcore
  rw [hlabel] at hstep ⊢
  omega

def IsD4ReversePath {m : ℕ} {tiling : D4LiteralTiling m}
    (label : MicroLabel) :
    SimplexPoint (m + 2) → SimplexPoint (m + 2) →
      List (D4GoodBonePlacement tiling) → Prop
  | terminal, core, [] => terminal = core
  | terminal, core, edge :: rest =>
      edge.target = terminal ∧ edge.label = label ∧
        IsD4ReversePath label edge.source core rest

noncomputable def d4ReversePathFromEdgeData {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    {edges : List (D4GoodBonePlacement tiling) //
      IsD4ReversePath edge.label edge.target
        (d4DefectCore tiling edge.label) edges} :=
  if hcore : edge.source = d4DefectCore tiling edge.label then
    ⟨[edge], by simp [IsD4ReversePath, hcore]⟩
  else
    let previous := d4PreviousEdge edge hcore
    let rest := d4ReversePathFromEdgeData previous
    ⟨edge :: rest.1, by
      change edge.target = edge.target ∧ edge.label = edge.label ∧
        IsD4ReversePath edge.label edge.source
          (d4DefectCore tiling edge.label) rest.1
      refine ⟨rfl, rfl, ?_⟩
      rw [← d4PreviousEdge_label edge hcore,
        ← d4PreviousEdge_target edge hcore]
      exact rest.2⟩
termination_by d4LabelRank edge.label edge.source
decreasing_by exact d4PreviousEdge_rank_lt edge hcore

noncomputable def d4ReversePathFromEdge {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    List (D4GoodBonePlacement tiling) :=
  (d4ReversePathFromEdgeData edge).1

theorem d4ReversePathFromEdge_spec {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    IsD4ReversePath edge.label edge.target
      (d4DefectCore tiling edge.label) (d4ReversePathFromEdge edge) :=
  (d4ReversePathFromEdgeData edge).2

noncomputable def d4BoundaryLastEdge {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel)
    (hnotcore : d4BoundaryOwner m label ≠ d4DefectCore tiling label) :
    D4GoodBonePlacement tiling :=
  ((d4_boundary_predecessor_or_core m tiling label).resolve_left hnotcore).choose

theorem d4BoundaryLastEdge_target {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel)
    (hnotcore : d4BoundaryOwner m label ≠ d4DefectCore tiling label) :
    (d4BoundaryLastEdge tiling label hnotcore).target =
      d4BoundaryOwner m label :=
  ((d4_boundary_predecessor_or_core m tiling label).resolve_left
    hnotcore).choose_spec.1.1

theorem d4BoundaryLastEdge_label {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel)
    (hnotcore : d4BoundaryOwner m label ≠ d4DefectCore tiling label) :
    (d4BoundaryLastEdge tiling label hnotcore).label = label :=
  ((d4_boundary_predecessor_or_core m tiling label).resolve_left
    hnotcore).choose_spec.1.2

noncomputable def d4ReverseBoundaryPath {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    List (D4GoodBonePlacement tiling) :=
  if hcore : d4BoundaryOwner m label = d4DefectCore tiling label then
    []
  else d4ReversePathFromEdge (d4BoundaryLastEdge tiling label hcore)

theorem d4ReverseBoundaryPath_spec {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    IsD4ReversePath label (d4BoundaryOwner m label)
      (d4DefectCore tiling label) (d4ReverseBoundaryPath tiling label) := by
  rw [d4ReverseBoundaryPath]
  split_ifs with hcore
  · exact hcore
  · have hspec := d4ReversePathFromEdge_spec
      (d4BoundaryLastEdge tiling label hcore)
    rw [d4BoundaryLastEdge_label tiling label hcore] at hspec
    rw [d4BoundaryLastEdge_target tiling label hcore] at hspec
    exact hspec

theorem d4ReverseBoundaryPath_labels {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    ∀ edge ∈ d4ReverseBoundaryPath tiling label, edge.label = label := by
  have all_labels {terminal core : SimplexPoint (m + 2)}
      {edges : List (D4GoodBonePlacement tiling)}
      (hpath : IsD4ReversePath label terminal core edges) :
      ∀ edge ∈ edges, edge.label = label := by
    induction edges generalizing terminal with
    | nil => simp
    | cons first rest ih =>
        simp only [IsD4ReversePath] at hpath
        intro edge hedge
        simp only [List.mem_cons] at hedge
        rcases hedge with rfl | hedge
        · exact hpath.2.1
        · exact ih hpath.2.2 edge hedge
  exact all_labels (d4ReverseBoundaryPath_spec tiling label)

end FiniteDefects
