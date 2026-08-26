import FiniteDefects.D4LeftInverse
import FiniteDefects.D4BallotWordEquiv

/-! # Encoding each literal arm as a concrete ballot word -/

namespace FiniteDefects

def d4ReverseMove : GoodBoneClass → BallotMove
  | .boneA0 => .minority
  | .boneA2 => .majority
  | .boneB0 => .majority
  | .boneB1 => .minority
  | .boneC0 => .minority
  | .boneC2 => .majority

def d4ArmWord {m : ℕ} (edges : List (D4LiteralDirectedEdge m)) :
    List BallotMove := edges.map fun edge => d4ReverseMove edge.boneClass

abbrev D4ArmPath (m : ℕ) (label : MicroLabel)
    (core : SimplexPoint (m + 2)) :=
  {edges : List (D4LiteralDirectedEdge m) //
    IsD4AbstractReversePath label (d4BoundaryOwner m label) core edges}

theorem d4_zero_edge_count_delta {m : ℕ} (edge : D4LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .zero) :
    (if d4ReverseMove edge.boneClass = .majority then 1 else 0) +
        edge.target.u + edge.target.v = edge.source.u + edge.source.v ∧
      (if d4ReverseMove edge.boneClass = .minority then 1 else 0) +
        edge.target.v = edge.source.v := by
  have hstep := d4LiteralDirectedEdge_simplex_step edge
  rcases hc : edge.boneClass with _ | _ | _ | _ | _ | _
  all_goals simp [hc, GoodBoneClass.label] at hlabel
  all_goals simp [hc, GoodBoneClass.step, stepA, stepB, stepC,
    d4ReverseMove] at hstep ⊢
  all_goals omega

theorem d4_one_edge_count_delta {m : ℕ} (edge : D4LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .one) :
    (if d4ReverseMove edge.boneClass = .majority then 1 else 0) +
        edge.target.v + edge.target.w = edge.source.v + edge.source.w ∧
      (if d4ReverseMove edge.boneClass = .minority then 1 else 0) +
        edge.target.w = edge.source.w := by
  have hstep := d4LiteralDirectedEdge_simplex_step edge
  rcases hc : edge.boneClass with _ | _ | _ | _ | _ | _
  all_goals simp [hc, GoodBoneClass.label] at hlabel
  all_goals simp [hc, GoodBoneClass.step, stepA, stepB, stepC,
    d4ReverseMove] at hstep ⊢
  all_goals omega

theorem d4_two_edge_count_delta {m : ℕ} (edge : D4LiteralDirectedEdge m)
    (hlabel : edge.boneClass.label = .two) :
    (if d4ReverseMove edge.boneClass = .majority then 1 else 0) +
        edge.target.w + edge.target.u = edge.source.w + edge.source.u ∧
      (if d4ReverseMove edge.boneClass = .minority then 1 else 0) +
        edge.target.u = edge.source.u := by
  have hstep := d4LiteralDirectedEdge_simplex_step edge
  rcases hc : edge.boneClass with _ | _ | _ | _ | _ | _
  all_goals simp [hc, GoodBoneClass.label] at hlabel
  all_goals simp [hc, GoodBoneClass.step, stepA, stepB, stepC,
    d4ReverseMove] at hstep ⊢
  all_goals omega

theorem d4_zero_word_counts {m : ℕ}
    {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath .zero terminal core edges) :
    majorityCount (d4ArmWord edges) + terminal.u + terminal.v =
        core.u + core.v ∧
      minorityCount (d4ArmWord edges) + terminal.v = core.v := by
  induction edges generalizing terminal with
  | nil =>
      simp only [IsD4AbstractReversePath] at hpath
      subst terminal
      simp [d4ArmWord, majorityCount, minorityCount]
  | cons edge rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      rcases ih hpath.2.2 with ⟨hmajor, hminor⟩
      have hlabel := hpath.2.1
      have hterminal := hpath.1
      have htu := congrArg SimplexPoint.u hterminal
      have htv := congrArg SimplexPoint.v hterminal
      have htw := congrArg SimplexPoint.w hterminal
      have hdelta := d4_zero_edge_count_delta edge hlabel
      have hmajCons : majorityCount (d4ArmWord (edge :: rest)) =
          (if d4ReverseMove edge.boneClass = .majority then 1 else 0) +
            majorityCount (d4ArmWord rest) := by
        rcases hmove : d4ReverseMove edge.boneClass with _ | _ <;>
          simp [d4ArmWord, majorityCount, hmove]; omega
      have hminCons : minorityCount (d4ArmWord (edge :: rest)) =
          (if d4ReverseMove edge.boneClass = .minority then 1 else 0) +
            minorityCount (d4ArmWord rest) := by
        rcases hmove : d4ReverseMove edge.boneClass with _ | _ <;>
          simp [d4ArmWord, minorityCount, hmove]; omega
      omega

theorem d4_one_word_counts {m : ℕ}
    {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath .one terminal core edges) :
    majorityCount (d4ArmWord edges) + terminal.v + terminal.w =
        core.v + core.w ∧
      minorityCount (d4ArmWord edges) + terminal.w = core.w := by
  induction edges generalizing terminal with
  | nil =>
      simp only [IsD4AbstractReversePath] at hpath
      subst terminal
      simp [d4ArmWord, majorityCount, minorityCount]
  | cons edge rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      rcases ih hpath.2.2 with ⟨hmajor, hminor⟩
      have hlabel := hpath.2.1
      have hterminal := hpath.1
      have htu := congrArg SimplexPoint.u hterminal
      have htv := congrArg SimplexPoint.v hterminal
      have htw := congrArg SimplexPoint.w hterminal
      have hdelta := d4_one_edge_count_delta edge hlabel
      have hmajCons : majorityCount (d4ArmWord (edge :: rest)) =
          (if d4ReverseMove edge.boneClass = .majority then 1 else 0) +
            majorityCount (d4ArmWord rest) := by
        rcases hmove : d4ReverseMove edge.boneClass with _ | _ <;>
          simp [d4ArmWord, majorityCount, hmove]; omega
      have hminCons : minorityCount (d4ArmWord (edge :: rest)) =
          (if d4ReverseMove edge.boneClass = .minority then 1 else 0) +
            minorityCount (d4ArmWord rest) := by
        rcases hmove : d4ReverseMove edge.boneClass with _ | _ <;>
          simp [d4ArmWord, minorityCount, hmove]; omega
      omega

theorem d4_two_word_counts {m : ℕ}
    {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath .two terminal core edges) :
    majorityCount (d4ArmWord edges) + terminal.w + terminal.u =
        core.w + core.u ∧
      minorityCount (d4ArmWord edges) + terminal.u = core.u := by
  induction edges generalizing terminal with
  | nil =>
      simp only [IsD4AbstractReversePath] at hpath
      subst terminal
      simp [d4ArmWord, majorityCount, minorityCount]
  | cons edge rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      rcases ih hpath.2.2 with ⟨hmajor, hminor⟩
      have hlabel := hpath.2.1
      have hterminal := hpath.1
      have htu := congrArg SimplexPoint.u hterminal
      have htv := congrArg SimplexPoint.v hterminal
      have htw := congrArg SimplexPoint.w hterminal
      have hdelta := d4_two_edge_count_delta edge hlabel
      have hmajCons : majorityCount (d4ArmWord (edge :: rest)) =
          (if d4ReverseMove edge.boneClass = .majority then 1 else 0) +
            majorityCount (d4ArmWord rest) := by
        rcases hmove : d4ReverseMove edge.boneClass with _ | _ <;>
          simp [d4ArmWord, majorityCount, hmove]; omega
      have hminCons : minorityCount (d4ArmWord (edge :: rest)) =
          (if d4ReverseMove edge.boneClass = .minority then 1 else 0) +
            minorityCount (d4ArmWord rest) := by
        rcases hmove : d4ReverseMove edge.boneClass with _ | _ <;>
          simp [d4ArmWord, minorityCount, hmove]; omega
      omega

theorem d4ReversePath_prefix {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges pre : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges)
    (hprefix : pre <+: edges) :
    ∃ endpoint, IsD4AbstractReversePath label terminal endpoint pre := by
  induction pre generalizing terminal edges with
  | nil => exact ⟨terminal, rfl⟩
  | cons head rest ih =>
      cases edges with
      | nil => simp at hprefix
      | cons edge edges =>
          simp only [List.cons_prefix_cons] at hprefix
          rcases hprefix with ⟨hhead, htail⟩
          subst edge
          simp only [IsD4AbstractReversePath] at hpath
          obtain ⟨endpoint, hrest⟩ := ih hpath.2.2 htail
          exact ⟨endpoint, ⟨hpath.1, hpath.2.1, hrest⟩⟩

theorem isBallotSequence_of_prefix_counts (word : List BallotMove)
    (hprefix : ∀ pre, pre <+: word →
      minorityCount pre ≤ majorityCount pre) :
    IsBallotSequence word := by
  induction word using List.reverseRecOn with
  | nil => exact IsBallotSequence.nil
  | append_singleton word move ih =>
      have hwordPrefix : ∀ pre, pre <+: word →
          minorityCount pre ≤ majorityCount pre := by
        intro pre hp
        exact hprefix pre (hp.trans (List.prefix_append word [move]))
      have ihword := ih hwordPrefix
      rcases move with _ | _
      · exact IsBallotSequence.appendMajority ihword
      · apply IsBallotSequence.appendMinority ihword
        have hfull := hprefix (word ++ [.minority]) (by rfl)
        have hfull' : minorityCount word + 1 ≤ majorityCount word := by
          simpa [minorityCount, majorityCount] using hfull
        omega

theorem d4ArmWord_prefix_ballot {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (path : D4ArmPath m label core) :
    ∀ pre, pre <+: d4ArmWord path.1 →
      minorityCount pre ≤ majorityCount pre := by
  intro pre hprefix
  have hlen : pre.length ≤ (d4ArmWord path.1).length := hprefix.length_le
  let edgePrefix := path.1.take pre.length
  have hedgePrefix : edgePrefix <+: path.1 := List.take_prefix _ _
  obtain ⟨endpoint, hpathPrefix⟩ := d4ReversePath_prefix path.2 hedgePrefix
  have hprefixEq : pre = d4ArmWord edgePrefix := by
    rw [List.prefix_iff_eq_take] at hprefix
    rw [hprefix]
    simp [d4ArmWord, edgePrefix]
  rw [hprefixEq]
  rcases label with _ | _ | _
  · have hcounts := d4_zero_word_counts hpathPrefix
    simp [d4BoundaryOwner, cornerW] at hcounts
    omega
  · have hcounts := d4_one_word_counts hpathPrefix
    simp [d4BoundaryOwner, cornerU] at hcounts
    omega
  · have hcounts := d4_two_word_counts hpathPrefix
    simp [d4BoundaryOwner, cornerV] at hcounts
    omega

noncomputable def d4ArmPathToConcrete {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (path : D4ArmPath m label core) :
    ConcreteBallotWord
      (match label with
       | .zero => core.u + core.v
       | .one => core.v + core.w
       | .two => core.w + core.u)
      (match label with
       | .zero => core.v
       | .one => core.w
       | .two => core.u) where
  word := d4ArmWord path.1
  majority_eq := by
    rcases label with _ | _ | _
    · have h := d4_zero_word_counts path.2
      simpa [d4BoundaryOwner, cornerW] using h.1
    · have h := d4_one_word_counts path.2
      simpa [d4BoundaryOwner, cornerU] using h.1
    · have h := d4_two_word_counts path.2
      simpa [d4BoundaryOwner, cornerV] using h.1
  minority_eq := by
    rcases label with _ | _ | _
    · have h := d4_zero_word_counts path.2
      simpa [d4BoundaryOwner, cornerW] using h.2
    · have h := d4_one_word_counts path.2
      simpa [d4BoundaryOwner, cornerU] using h.2
    · have h := d4_two_word_counts path.2
      simpa [d4BoundaryOwner, cornerV] using h.2
  ballot := isBallotSequence_of_prefix_counts _
    (d4ArmWord_prefix_ballot label core path)

end FiniteDefects
