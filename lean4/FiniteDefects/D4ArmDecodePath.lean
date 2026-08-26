import FiniteDefects.D4ArmDecode

/-! # Decoding a whole concrete ballot word into a literal arm -/

namespace FiniteDefects

@[simp] theorem d4ArmEdge_boneClass {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (move : BallotMove)
    (hp : pre ++ [move] <+: data.word) :
    (d4ArmEdge label core hroom data pre move hp).boneClass =
      d4GoodBoneClassOfReverseMove label move := by
  rfl

@[simp] theorem d4ArmEdge_source {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (move : BallotMove)
    (hp : pre ++ [move] <+: data.word) :
    (d4ArmEdge label core hroom data pre move hp).source =
      d4ArmPoint label core data (pre ++ [move]) hp := by
  rfl

@[simp] theorem d4ArmEdge_target {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (move : BallotMove)
    (hp : pre ++ [move] <+: data.word) :
    (d4ArmEdge label core hroom data pre move hp).target =
      d4ArmPoint label core data pre
        ((List.prefix_append pre [move]).trans hp) := by
  rfl

noncomputable def d4DecodeArmEdgesAux {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre suffix : List BallotMove) (hword : pre ++ suffix = data.word) :
    List (D4LiteralDirectedEdge m) :=
  match suffix with
  | [] => []
  | move :: rest =>
      have hp : pre ++ [move] <+: data.word := by
        rw [← hword]
        exact ⟨rest, by simp [List.append_assoc]⟩
      have hnext : (pre ++ [move]) ++ rest = data.word := by
        simpa [List.append_assoc] using hword
      d4ArmEdge label core hroom data pre move hp ::
        d4DecodeArmEdgesAux label core hroom data
          (pre ++ [move]) rest hnext
termination_by suffix.length

theorem d4DecodeArmEdgesAux_path {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre suffix : List BallotMove) (hword : pre ++ suffix = data.word) :
    IsD4AbstractReversePath label
      (d4ArmPoint label core data pre (by
        rw [← hword]
        exact List.prefix_append pre suffix))
      core (d4DecodeArmEdgesAux label core hroom data pre suffix hword) := by
  induction suffix generalizing pre with
  | nil =>
      have hpre : pre = data.word := by simpa using hword
      subst pre
      simpa [d4DecodeArmEdgesAux] using
        d4ArmPoint_full label core data (by rfl)
  | cons move rest ih =>
      have hp : pre ++ [move] <+: data.word := by
        rw [← hword]
        exact ⟨rest, by simp [List.append_assoc]⟩
      have hnext : (pre ++ [move]) ++ rest = data.word := by
        simpa [List.append_assoc] using hword
      have htail := ih (pre := pre ++ [move]) hnext
      simp only [d4DecodeArmEdgesAux, IsD4AbstractReversePath]
      refine ⟨?_, ?_, ?_⟩
      · exact d4ArmEdge_target label core hroom data pre move hp
      · simp
      · simpa only [d4ArmEdge_source] using htail

theorem d4DecodeArmEdgesAux_word {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre suffix : List BallotMove) (hword : pre ++ suffix = data.word) :
    d4ArmWord (d4DecodeArmEdgesAux label core hroom data pre suffix hword) =
      suffix := by
  induction suffix generalizing pre with
  | nil => simp [d4DecodeArmEdgesAux, d4ArmWord]
  | cons move rest ih =>
      have hnext : (pre ++ [move]) ++ rest = data.word := by
        simpa [List.append_assoc] using hword
      simp only [d4DecodeArmEdgesAux, d4ArmWord, List.map_cons]
      rw [d4ArmEdge_boneClass]
      rw [d4GoodBoneClassOfReverseMove_move]
      apply congrArg (List.cons move)
      simpa only [d4ArmWord] using ih (pre := pre ++ [move]) hnext

noncomputable def d4ConcreteToArmPath {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core)) : D4ArmPath m label core :=
  ⟨d4DecodeArmEdgesAux label core hroom data [] data.word (by simp), by
    have hpath := d4DecodeArmEdgesAux_path label core hroom data
      [] data.word (by simp)
    rw [d4ArmPoint_nil] at hpath
    exact hpath⟩

@[simp] theorem d4ConcreteToArmPath_word {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core)) :
    d4ArmWord (d4ConcreteToArmPath label core hroom data).1 = data.word := by
  exact d4DecodeArmEdgesAux_word label core hroom data [] data.word (by simp)

noncomputable def d4ArmPathToConcreteExact {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (path : D4ArmPath m label core) :
    ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core) where
  word := d4ArmWord path.1
  majority_eq := by
    rcases label with _ | _ | _
    · have h := d4_zero_word_counts path.2
      simpa [d4BoundaryOwner, cornerW, d4ArmMajority] using h.1
    · have h := d4_one_word_counts path.2
      simpa [d4BoundaryOwner, cornerU, d4ArmMajority] using h.1
    · have h := d4_two_word_counts path.2
      simpa [d4BoundaryOwner, cornerV, d4ArmMajority] using h.1
  minority_eq := by
    rcases label with _ | _ | _
    · have h := d4_zero_word_counts path.2
      simpa [d4BoundaryOwner, cornerW, d4ArmMinority] using h.2
    · have h := d4_one_word_counts path.2
      simpa [d4BoundaryOwner, cornerU, d4ArmMinority] using h.2
    · have h := d4_two_word_counts path.2
      simpa [d4BoundaryOwner, cornerV, d4ArmMinority] using h.2
  ballot := isBallotSequence_of_prefix_counts _
    (d4ArmWord_prefix_ballot label core path)

@[simp] theorem d4ArmPathToConcreteExact_word {m : ℕ}
    (label : MicroLabel) (core : SimplexPoint (m + 2))
    (path : D4ArmPath m label core) :
    (d4ArmPathToConcreteExact label core path).word = d4ArmWord path.1 := by
  rfl

@[simp] theorem d4ArmPathToConcrete_decode {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core)) :
    d4ArmPathToConcreteExact label core
      (d4ConcreteToArmPath label core hroom data) = data := by
  apply ConcreteBallotWord.ext
  exact d4ConcreteToArmPath_word label core hroom data

end FiniteDefects
