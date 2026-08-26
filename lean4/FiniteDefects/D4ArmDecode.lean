import FiniteDefects.D4ArmWords

/-! # Decoding a concrete ballot word into a literal directed arm -/

namespace FiniteDefects

def d4ArmMajority {t : ℕ} (label : MicroLabel) (core : SimplexPoint t) : ℕ :=
  match label with
  | .zero => core.u + core.v
  | .one => core.v + core.w
  | .two => core.w + core.u

def d4ArmMinority {t : ℕ} (label : MicroLabel) (core : SimplexPoint t) : ℕ :=
  match label with
  | .zero => core.v
  | .one => core.w
  | .two => core.u

def d4ArmRoom {t : ℕ} (label : MicroLabel) (core : SimplexPoint t) : Prop :=
  d4ArmMajority label core < t

def d4GoodBoneClassOfReverseMove : MicroLabel → BallotMove → GoodBoneClass
  | .zero, .majority => .boneC2
  | .zero, .minority => .boneC0
  | .one, .majority => .boneB0
  | .one, .minority => .boneB1
  | .two, .majority => .boneA2
  | .two, .minority => .boneA0

@[simp] theorem d4GoodBoneClassOfReverseMove_label
    (label : MicroLabel) (move : BallotMove) :
    (d4GoodBoneClassOfReverseMove label move).label = label := by
  rcases label <;> rcases move <;> rfl

@[simp] theorem d4GoodBoneClassOfReverseMove_move
    (label : MicroLabel) (move : BallotMove) :
    d4ReverseMove (d4GoodBoneClassOfReverseMove label move) = move := by
  rcases label <;> rcases move <;> rfl

theorem d4ArmPrefix_majority_le {up down : ℕ}
    (data : ConcreteBallotWord up down) {pre : List BallotMove}
    (hp : pre <+: data.word) : majorityCount pre ≤ up := by
  rw [← data.majority_eq]
  exact majorityCount_prefix_le hp

theorem d4ArmPrefix_ballot {up down : ℕ}
    (data : ConcreteBallotWord up down) {pre : List BallotMove}
    (hp : pre <+: data.word) : minorityCount pre ≤ majorityCount pre :=
  (data.ballot.prefix_closed hp).count_le

noncomputable def d4ArmPoint {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2))
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (hp : pre <+: data.word) :
    SimplexPoint (m + 2) := by
  have hballot := d4ArmPrefix_ballot data hp
  have hmajor := d4ArmPrefix_majority_le data hp
  simp only [majorityCount, minorityCount] at hballot hmajor
  have hsub := Nat.sub_add_cancel hballot
  have hcoreSum := core.sum_eq
  rcases label with _ | _ | _
  · exact
      { u := pre.count .majority - pre.count .minority
        v := pre.count .minority
        w := m + 2 - pre.count .majority
        sum_eq := by simp [d4ArmMajority] at hmajor; omega }
  · exact
      { u := m + 2 - pre.count .majority
        v := pre.count .majority - pre.count .minority
        w := pre.count .minority
        sum_eq := by simp [d4ArmMajority] at hmajor; omega }
  · exact
      { u := pre.count .minority
        v := m + 2 - pre.count .majority
        w := pre.count .majority - pre.count .minority
        sum_eq := by simp [d4ArmMajority] at hmajor; omega }

theorem d4ArmPoint_zero_coordinates {m : ℕ}
    (core : SimplexPoint (m + 2))
    (data : ConcreteBallotWord (d4ArmMajority .zero core)
      (d4ArmMinority .zero core))
    (pre : List BallotMove) (hp : pre <+: data.word) :
    (d4ArmPoint .zero core data pre hp).u =
        pre.count .majority - pre.count .minority ∧
      (d4ArmPoint .zero core data pre hp).v = pre.count .minority ∧
      (d4ArmPoint .zero core data pre hp).w =
        m + 2 - pre.count .majority := by exact ⟨rfl, rfl, rfl⟩

theorem d4ArmPoint_one_coordinates {m : ℕ}
    (core : SimplexPoint (m + 2))
    (data : ConcreteBallotWord (d4ArmMajority .one core)
      (d4ArmMinority .one core))
    (pre : List BallotMove) (hp : pre <+: data.word) :
    (d4ArmPoint .one core data pre hp).u =
        m + 2 - pre.count .majority ∧
      (d4ArmPoint .one core data pre hp).v =
        pre.count .majority - pre.count .minority ∧
      (d4ArmPoint .one core data pre hp).w = pre.count .minority := by
  exact ⟨rfl, rfl, rfl⟩

theorem d4ArmPoint_two_coordinates {m : ℕ}
    (core : SimplexPoint (m + 2))
    (data : ConcreteBallotWord (d4ArmMajority .two core)
      (d4ArmMinority .two core))
    (pre : List BallotMove) (hp : pre <+: data.word) :
    (d4ArmPoint .two core data pre hp).u = pre.count .minority ∧
      (d4ArmPoint .two core data pre hp).v =
        m + 2 - pre.count .majority ∧
      (d4ArmPoint .two core data pre hp).w =
        pre.count .majority - pre.count .minority := by exact ⟨rfl, rfl, rfl⟩

theorem d4ArmPoint_nil {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2))
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (hp : [] <+: data.word) :
    d4ArmPoint label core data [] hp = d4BoundaryOwner m label := by
  rcases label <;>
    apply simplexPoint_ext <;>
    simp [d4ArmPoint, d4BoundaryOwner, cornerU, cornerV, cornerW,
      majorityCount, minorityCount]

theorem d4ArmPoint_full {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2))
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (hp : data.word <+: data.word) :
    d4ArmPoint label core data data.word hp = core := by
  have hsum := core.sum_eq
  have hmajor := data.majority_eq
  have hminor := data.minority_eq
  simp only [majorityCount, minorityCount] at hmajor hminor
  have hballot := data.ballot.count_le
  simp only [majorityCount, minorityCount] at hballot
  have hsub := Nat.sub_add_cancel hballot
  rcases label <;>
    apply simplexPoint_ext <;>
    simp [d4ArmPoint, d4ArmMajority, d4ArmMinority,
      hmajor, hminor] <;>
    omega

theorem d4ArmPoint_full_owner {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (hp : pre <+: data.word)
    (hne : pre ≠ []) : IsD4FullOwner (d4ArmPoint label core data pre hp) := by
  have hballot := d4ArmPrefix_ballot data hp
  have hmajor := d4ArmPrefix_majority_le data hp
  simp only [majorityCount, minorityCount] at hballot hmajor
  have hsub := Nat.sub_add_cancel hballot
  have hcoreSum := core.sum_eq
  have hpositive : 0 < pre.count .majority := by
    cases hpre : pre with
    | nil => exact (hne hpre).elim
    | cons move rest =>
        rcases move with _ | _
        · simp [majorityCount]
        · have hsingle : [BallotMove.minority] <+: pre := by
            rw [hpre]
            simp
          have hcount := ((data.ballot.prefix_closed hp).prefix_closed
            hsingle).count_le
          simp [majorityCount, minorityCount] at hcount
  have hcomplementLt : m + 2 - pre.count .majority < m + 2 :=
    Nat.sub_lt (by omega) hpositive
  rcases label with _ | _ | _
  · simp [d4ArmRoom, d4ArmMajority] at hroom hmajor
    have hmajLt : pre.count .majority < m + 2 :=
      lt_of_le_of_lt hmajor hroom
    have hminLt := lt_of_le_of_lt hballot hmajLt
    have hdiffLt : pre.count .majority - pre.count .minority < m + 2 :=
      lt_of_le_of_lt (Nat.sub_le _ _) hmajLt
    apply d4_interior_is_full
    · simpa [d4ArmPoint] using hdiffLt
    · simpa [d4ArmPoint] using hminLt
    · simpa [d4ArmPoint] using hcomplementLt
  · simp [d4ArmRoom, d4ArmMajority] at hroom hmajor
    have hmajLt : pre.count .majority < m + 2 :=
      lt_of_le_of_lt hmajor hroom
    have hminLt := lt_of_le_of_lt hballot hmajLt
    have hdiffLt : pre.count .majority - pre.count .minority < m + 2 :=
      lt_of_le_of_lt (Nat.sub_le _ _) hmajLt
    apply d4_interior_is_full
    · simpa [d4ArmPoint] using hcomplementLt
    · simpa [d4ArmPoint] using hdiffLt
    · simpa [d4ArmPoint] using hminLt
  · simp [d4ArmRoom, d4ArmMajority] at hroom hmajor
    have hmajLt : pre.count .majority < m + 2 :=
      lt_of_le_of_lt hmajor hroom
    have hminLt := lt_of_le_of_lt hballot hmajLt
    have hdiffLt : pre.count .majority - pre.count .minority < m + 2 :=
      lt_of_le_of_lt (Nat.sub_le _ _) hmajLt
    apply d4_interior_is_full
    · simpa [d4ArmPoint] using hminLt
    · simpa [d4ArmPoint] using hcomplementLt
    · simpa [d4ArmPoint] using hdiffLt

theorem d4ArmPoint_label_present {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (hp : pre <+: data.word) :
    inBenzel (m + 4) (2 * m + 4)
      (ownerCell (d4ArmPoint label core data pre hp) label) := by
  by_cases hnil : pre = []
  · subst pre
    rw [d4ArmPoint_nil]
    exact d4BoundaryOwner_present m label
  · exact (d4ArmPoint_full_owner label core hroom data pre hp hnil) label

@[simp] theorem count_majority_append_majority (pre : List BallotMove) :
    (pre ++ [BallotMove.majority]).count BallotMove.majority =
      pre.count BallotMove.majority + 1 := by
  rw [List.count_append]
  simp only [List.count_cons, List.count_nil, Nat.add_zero]
  rw [show (BallotMove.majority == BallotMove.majority) = true by decide]
  simp

@[simp] theorem count_minority_append_majority (pre : List BallotMove) :
    (pre ++ [BallotMove.majority]).count BallotMove.minority =
      pre.count BallotMove.minority := by
  rw [List.count_append]
  simp only [List.count_cons, List.count_nil, Nat.add_zero]
  rw [show (BallotMove.majority == BallotMove.minority) = false by decide]
  simp

@[simp] theorem count_majority_append_minority (pre : List BallotMove) :
    (pre ++ [BallotMove.minority]).count BallotMove.majority =
      pre.count BallotMove.majority := by
  rw [List.count_append]
  simp only [List.count_cons, List.count_nil, Nat.add_zero]
  rw [show (BallotMove.minority == BallotMove.majority) = false by decide]
  simp

@[simp] theorem count_minority_append_minority (pre : List BallotMove) :
    (pre ++ [BallotMove.minority]).count BallotMove.minority =
      pre.count BallotMove.minority + 1 := by
  rw [List.count_append]
  simp only [List.count_cons, List.count_nil, Nat.add_zero]
  rw [show (BallotMove.minority == BallotMove.minority) = true by decide]
  simp

theorem stepA_anchor_of_coordinates {t : ℕ} (source target : SimplexPoint t)
    (h : target.u + 1 = source.u ∧ target.v = source.v ∧
      target.w = source.w + 1) :
    addCell (ownerQ source, ownerR source) stepA =
      (ownerQ target, ownerR target) := by
  apply Prod.ext <;> simp [addCell, stepA, ownerQ, ownerR] <;> omega

theorem stepB_anchor_of_coordinates {t : ℕ} (source target : SimplexPoint t)
    (h : target.u = source.u ∧ target.v = source.v + 1 ∧
      target.w + 1 = source.w) :
    addCell (ownerQ source, ownerR source) stepB =
      (ownerQ target, ownerR target) := by
  apply Prod.ext <;> simp [addCell, stepB, ownerQ, ownerR] <;> omega

theorem stepC_anchor_of_coordinates {t : ℕ} (source target : SimplexPoint t)
    (h : target.u = source.u + 1 ∧ target.v + 1 = source.v ∧
      target.w = source.w) :
    addCell (ownerQ source, ownerR source) stepC =
      (ownerQ target, ownerR target) := by
  apply Prod.ext <;> simp [addCell, stepC, ownerQ, ownerR] <;> omega

theorem d4ArmPoint_append_step {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (move : BallotMove)
    (hp : pre ++ [move] <+: data.word) :
    addCell
      (ownerQ (d4ArmPoint label core data (pre ++ [move]) hp),
        ownerR (d4ArmPoint label core data (pre ++ [move]) hp))
      (d4GoodBoneClassOfReverseMove label move).step =
      (ownerQ (d4ArmPoint label core data pre
        ((List.prefix_append pre [move]).trans hp)),
       ownerR (d4ArmPoint label core data pre
        ((List.prefix_append pre [move]).trans hp))) := by
  have hp0 := (List.prefix_append pre [move]).trans hp
  have hmajorAppend := d4ArmPrefix_majority_le data hp
  simp only [majorityCount] at hmajorAppend
  have hmajorAppendLt : (pre ++ [move]).count .majority < m + 2 :=
    lt_of_le_of_lt hmajorAppend hroom
  have hballotAppend := d4ArmPrefix_ballot data hp
  simp only [majorityCount, minorityCount] at hballotAppend
  have hsubAppend := Nat.sub_add_cancel hballotAppend
  have hballotPre := d4ArmPrefix_ballot data hp0
  simp only [majorityCount, minorityCount] at hballotPre
  have hsubPre := Nat.sub_add_cancel hballotPre
  rcases label with _ | _ | _
  · have hs := d4ArmPoint_zero_coordinates core data (pre ++ [move]) hp
    have ht := d4ArmPoint_zero_coordinates core data pre hp0
    rcases move with _ | _
    · rw [count_majority_append_majority] at hmajorAppendLt
      rw [count_majority_append_majority,
        count_minority_append_majority] at hs hsubAppend
      apply stepA_anchor_of_coordinates
      rcases hs with ⟨hsu, hsv, hsw⟩
      rcases ht with ⟨htu, htv, htw⟩
      exact ⟨by omega, by omega, by omega⟩
    · rw [count_majority_append_minority] at hmajorAppendLt
      rw [count_majority_append_minority,
        count_minority_append_minority] at hs hsubAppend
      apply stepC_anchor_of_coordinates
      rcases hs with ⟨hsu, hsv, hsw⟩
      rcases ht with ⟨htu, htv, htw⟩
      exact ⟨by omega, by omega, by omega⟩
  · have hs := d4ArmPoint_one_coordinates core data (pre ++ [move]) hp
    have ht := d4ArmPoint_one_coordinates core data pre hp0
    rcases move with _ | _
    · rw [count_majority_append_majority] at hmajorAppendLt
      rw [count_majority_append_majority,
        count_minority_append_majority] at hs hsubAppend
      apply stepC_anchor_of_coordinates
      rcases hs with ⟨hsu, hsv, hsw⟩
      rcases ht with ⟨htu, htv, htw⟩
      exact ⟨by omega, by omega, by omega⟩
    · rw [count_majority_append_minority] at hmajorAppendLt
      rw [count_majority_append_minority,
        count_minority_append_minority] at hs hsubAppend
      apply stepB_anchor_of_coordinates
      rcases hs with ⟨hsu, hsv, hsw⟩
      rcases ht with ⟨htu, htv, htw⟩
      exact ⟨by omega, by omega, by omega⟩
  · have hs := d4ArmPoint_two_coordinates core data (pre ++ [move]) hp
    have ht := d4ArmPoint_two_coordinates core data pre hp0
    rcases move with _ | _
    · rw [count_majority_append_majority] at hmajorAppendLt
      rw [count_majority_append_majority,
        count_minority_append_majority] at hs hsubAppend
      apply stepB_anchor_of_coordinates
      rcases hs with ⟨hsu, hsv, hsw⟩
      rcases ht with ⟨htu, htv, htw⟩
      exact ⟨by omega, by omega, by omega⟩
    · rw [count_majority_append_minority] at hmajorAppendLt
      rw [count_majority_append_minority,
        count_minority_append_minority] at hs hsubAppend
      apply stepA_anchor_of_coordinates
      rcases hs with ⟨hsu, hsv, hsw⟩
      rcases ht with ⟨htu, htv, htw⟩
      exact ⟨by omega, by omega, by omega⟩

theorem reverseBoneBase_residue {t : ℕ} (source : SimplexPoint t)
    (boneClass : GoodBoneClass) :
    placementBaseResidue t (reverseBoneBase source boneClass) =
      boneClass.residue := by
  have hphase := owner_phase_identity source
  rcases boneClass <;>
    unfold placementBaseResidue residueOfInt <;>
    simp only [reverseBoneBase, GoodBoneClass.sourceShift,
      GoodBoneClass.residue, Res3.value] <;>
    split_ifs <;> simp_all <;> omega

theorem d4ReverseBonePlacement_class {m : ℕ}
    (label : MicroLabel) (move : BallotMove)
    (source target : SimplexPoint (m + 2))
    (hstep : addCell (ownerQ source, ownerR source)
      (d4GoodBoneClassOfReverseMove label move).step =
      (ownerQ target, ownerR target))
    (hsource : IsD4FullOwner source)
    (htarget : inBenzel (m + 4) (2 * m + 4) (ownerCell target label)) :
    D4IsPlacementClass
      (d4ReverseBonePlacement source target
        (d4GoodBoneClassOfReverseMove label move) hstep
        (fun ell _ => hsource ell) (by simpa using htarget))
      (d4GoodBoneClassOfReverseMove label move) := by
  constructor
  · rfl
  · rw [d4ReverseBonePlacement_base]
    exact reverseBoneBase_residue source
      (d4GoodBoneClassOfReverseMove label move)

noncomputable def d4ArmEdge {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core)
    (data : ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (pre : List BallotMove) (move : BallotMove)
    (hp : pre ++ [move] <+: data.word) : D4LiteralDirectedEdge m := by
  let hp0 := (List.prefix_append pre [move]).trans hp
  let source := d4ArmPoint label core data (pre ++ [move]) hp
  let target := d4ArmPoint label core data pre hp0
  let boneClass := d4GoodBoneClassOfReverseMove label move
  have hsource : IsD4FullOwner source :=
    d4ArmPoint_full_owner label core hroom data (pre ++ [move]) hp (by simp)
  have htarget := d4ArmPoint_label_present label core hroom data pre hp0
  have hstep := d4ArmPoint_append_step label core hroom data pre move hp
  let placement := d4ReverseBonePlacement source target boneClass hstep
    (fun ell _ => hsource ell) (by simpa [boneClass] using htarget)
  have hclass : D4IsPlacementClass placement boneClass := by
    exact d4ReverseBonePlacement_class label move source target hstep
      hsource htarget
  exact
    { placement := placement
      boneClass := boneClass
      class_spec := hclass
      source := source
      target := target
      source_anchor := by
        rw [d4ReverseBonePlacement_base]
        have h := reverseBoneBase_source_anchor source boneClass
        exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
      target_anchor := by
        rw [d4ReverseBonePlacement_base]
        have h := reverseBoneBase_target_anchor source target boneClass hstep
        exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩ }

end FiniteDefects
