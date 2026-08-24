import BenzelProblem6Kernel.PositiveYCoverExistence
import Mathlib.Data.List.Nodup

/-!
# Counting the owners occupied by a reconstructed positive Y
-/

namespace BenzelProblem6Kernel

theorem inits_nodup {α : Type} (word : List α) : word.inits.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro left right heq
  apply Fin.ext
  have hl : left.1 ≤ word.length := by
    have := left.2
    simp at this
    omega
  have hr : right.1 ≤ word.length := by
    have := right.2
    simp at this
    omega
  have hlen := congrArg List.length heq
  simpa [Nat.min_eq_left hl, Nat.min_eq_left hr] using hlen

noncomputable def labelZeroPrefixOwnerList {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    List (SimplexPoint t) :=
  (recursiveBallotWord path).inits.attach.map fun pre =>
    labelZeroPrefixSimplexPoint path pre.1 (by simpa using pre.2) hup

noncomputable def labelOnePrefixOwnerList {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    List (SimplexPoint t) :=
  (recursiveBallotWord path).inits.attach.map fun pre =>
    labelOnePrefixSimplexPoint path pre.1 (by simpa using pre.2) hup

noncomputable def labelTwoPrefixOwnerList {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    List (SimplexPoint t) :=
  (recursiveBallotWord path).inits.attach.map fun pre =>
    labelTwoPrefixSimplexPoint path pre.1 (by simpa using pre.2) hup

@[simp] theorem labelZeroPrefixOwnerList_length {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    (labelZeroPrefixOwnerList path hup).length = up + down + 1 := by
  simp [labelZeroPrefixOwnerList, recursiveBallotWord_length]

@[simp] theorem labelOnePrefixOwnerList_length {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    (labelOnePrefixOwnerList path hup).length = up + down + 1 := by
  simp [labelOnePrefixOwnerList, recursiveBallotWord_length]

@[simp] theorem labelTwoPrefixOwnerList_length {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    (labelTwoPrefixOwnerList path hup).length = up + down + 1 := by
  simp [labelTwoPrefixOwnerList, recursiveBallotWord_length]

theorem labelZeroPrefixOwnerList_nodup {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    (labelZeroPrefixOwnerList path hup).Nodup := by
  apply List.Nodup.map_on
  · intro left _ right _ heq
    apply Subtype.ext
    apply labelZeroPrefixPoint_injective path left.1 right.1
      (by simpa using left.2) (by simpa using right.2)
    have hint := congrArg simplexPointToInt heq
    simpa [simplexPointToInt_labelZeroPrefixSimplexPoint] using hint
  · exact (inits_nodup (recursiveBallotWord path)).attach

theorem labelOnePrefixOwnerList_nodup {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    (labelOnePrefixOwnerList path hup).Nodup := by
  apply List.Nodup.map_on
  · intro left _ right _ heq
    apply Subtype.ext
    apply labelOnePrefixPoint_injective path left.1 right.1
      (by simpa using left.2) (by simpa using right.2)
    have hint := congrArg simplexPointToInt heq
    simpa [simplexPointToInt_labelOnePrefixSimplexPoint] using hint
  · exact (inits_nodup (recursiveBallotWord path)).attach

theorem labelTwoPrefixOwnerList_nodup {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t) :
    (labelTwoPrefixOwnerList path hup).Nodup := by
  apply List.Nodup.map_on
  · intro left _ right _ heq
    apply Subtype.ext
    apply labelTwoPrefixPoint_injective path left.1 right.1
      (by simpa using left.2) (by simpa using right.2)
    have hint := congrArg simplexPointToInt heq
    simpa [simplexPointToInt_labelTwoPrefixSimplexPoint] using hint
  · exact (inits_nodup (recursiveBallotWord path)).attach

theorem positive_labelZero_prefix_ne_sink (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1))
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    labelZeroPrefixSimplexPoint (t := x + y + z + 3)
      path pre hp (by omega) ≠ sinkPoint x y z := by
  intro heq
  have hbound := positive_labelZero_prefix_bounds x y z path pre hp
  have hv := labelZeroPrefixSimplexPoint_v (t := x + y + z + 3)
    path pre hp (by omega)
  have heqv := congrArg SimplexPoint.v heq
  simp [sinkPoint] at heqv
  have hv' :
      ((labelZeroPrefixSimplexPoint (t := x + y + z + 3)
        path pre hp (by omega)).v : ℤ) =
        (labelZeroPrefixPoint (x + y + z + 3) pre).v := hv
  omega

theorem positive_labelOne_prefix_ne_sink (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1))
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    labelOnePrefixSimplexPoint (t := x + y + z + 3)
      path pre hp (by omega) ≠ sinkPoint x y z := by
  intro heq
  have hbound := positive_labelOne_prefix_bounds x y z path pre hp
  have hw := labelOnePrefixSimplexPoint_w (t := x + y + z + 3)
    path pre hp (by omega)
  have heqw := congrArg SimplexPoint.w heq
  simp [sinkPoint] at heqw
  have hw' :
      ((labelOnePrefixSimplexPoint (t := x + y + z + 3)
        path pre hp (by omega)).w : ℤ) =
        (labelOnePrefixPoint (x + y + z + 3) pre).w := hw
  omega

theorem positive_labelTwo_prefix_ne_sink (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1))
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    labelTwoPrefixSimplexPoint (t := x + y + z + 3)
      path pre hp (by omega) ≠ sinkPoint x y z := by
  intro heq
  have hbound := positive_labelTwo_prefix_bounds x y z path pre hp
  have hu := labelTwoPrefixSimplexPoint_u (t := x + y + z + 3)
    path pre hp (by omega)
  have hequ := congrArg SimplexPoint.u heq
  simp [sinkPoint] at hequ
  have hu' :
      ((labelTwoPrefixSimplexPoint (t := x + y + z + 3)
        path pre hp (by omega)).u : ℤ) =
        (labelTwoPrefixPoint (x + y + z + 3) pre).u := hu
  omega

theorem mem_labelZeroPrefixOwnerList_iff {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t)
    (point : SimplexPoint t) :
    point ∈ labelZeroPrefixOwnerList path hup ↔
      ∃ (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path),
        point = labelZeroPrefixSimplexPoint path pre hp hup := by
  constructor
  · intro hmem
    simp only [labelZeroPrefixOwnerList, List.mem_map] at hmem
    obtain ⟨pre, _, rfl⟩ := hmem
    exact ⟨pre.1, by simpa using pre.2, rfl⟩
  · rintro ⟨pre, hp, rfl⟩
    simp only [labelZeroPrefixOwnerList, List.mem_map]
    have hinit : pre ∈ (recursiveBallotWord path).inits := by simpa using hp
    exact ⟨⟨pre, hinit⟩, by simp, rfl⟩

theorem mem_labelOnePrefixOwnerList_iff {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t)
    (point : SimplexPoint t) :
    point ∈ labelOnePrefixOwnerList path hup ↔
      ∃ (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path),
        point = labelOnePrefixSimplexPoint path pre hp hup := by
  constructor
  · intro hmem
    simp only [labelOnePrefixOwnerList, List.mem_map] at hmem
    obtain ⟨pre, _, rfl⟩ := hmem
    exact ⟨pre.1, by simpa using pre.2, rfl⟩
  · rintro ⟨pre, hp, rfl⟩
    simp only [labelOnePrefixOwnerList, List.mem_map]
    have hinit : pre ∈ (recursiveBallotWord path).inits := by simpa using hp
    exact ⟨⟨pre, hinit⟩, by simp, rfl⟩

theorem mem_labelTwoPrefixOwnerList_iff {up down t : ℕ}
    (path : RecursiveBallot up down) (hup : up ≤ t)
    (point : SimplexPoint t) :
    point ∈ labelTwoPrefixOwnerList path hup ↔
      ∃ (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path),
        point = labelTwoPrefixSimplexPoint path pre hp hup := by
  constructor
  · intro hmem
    simp only [labelTwoPrefixOwnerList, List.mem_map] at hmem
    obtain ⟨pre, _, rfl⟩ := hmem
    exact ⟨pre.1, by simpa using pre.2, rfl⟩
  · rintro ⟨pre, hp, rfl⟩
    simp only [labelTwoPrefixOwnerList, List.mem_map]
    have hinit : pre ∈ (recursiveBallotWord path).inits := by simpa using hp
    exact ⟨⟨pre, hinit⟩, by simp, rfl⟩

noncomputable def positiveYOwnerList (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    List (SimplexPoint (x + y + z + 3)) :=
  labelZeroPrefixOwnerList arms.1 (by omega) ++
    labelOnePrefixOwnerList arms.2.1 (by omega) ++
    labelTwoPrefixOwnerList arms.2.2 (by omega) ++
    [sinkPoint x y z]

@[simp] theorem positiveYOwnerList_length (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYOwnerList x y z arms).length =
      3 * (x + y + z + 3) + 1 := by
  simp [positiveYOwnerList]
  omega

theorem positive_zero_one_prefix_lists_disjoint (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega))
      (labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega)) := by
  rw [List.disjoint_left]
  intro point hzero hone
  obtain ⟨pre0, hp0, heq0⟩ :=
    (mem_labelZeroPrefixOwnerList_iff arms.1 (by omega) point).1 hzero
  obtain ⟨pre1, hp1, heq1⟩ :=
    (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) point).1 hone
  have hz : PositiveLabelZeroPoint x y z arms.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre0, hp0, by
      rw [heq0]
      exact simplexPointToInt_labelZeroPrefixSimplexPoint arms.1 pre0 hp0
        (by omega)⟩
  have ho : PositiveLabelOnePoint x y z arms.2.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre1, hp1, by
      rw [heq1]
      exact simplexPointToInt_labelOnePrefixSimplexPoint arms.2.1 pre1 hp1
        (by omega)⟩
  have hsink := positive_zero_one_owner_meet_only_at_sink x y z arms point hz ho
  rw [heq0] at hsink
  exact positive_labelZero_prefix_ne_sink x y z arms.1 pre0 hp0 hsink

theorem positive_one_two_prefix_lists_disjoint (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    List.Disjoint
      (labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega))
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega)) := by
  rw [List.disjoint_left]
  intro point hone htwo
  obtain ⟨pre1, hp1, heq1⟩ :=
    (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) point).1 hone
  obtain ⟨pre2, hp2, heq2⟩ :=
    (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) point).1 htwo
  have ho : PositiveLabelOnePoint x y z arms.2.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre1, hp1, by
      rw [heq1]
      exact simplexPointToInt_labelOnePrefixSimplexPoint arms.2.1 pre1 hp1
        (by omega)⟩
  have ht : PositiveLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point) := by
    right
    exact ⟨pre2, hp2, by
      rw [heq2]
      exact simplexPointToInt_labelTwoPrefixSimplexPoint arms.2.2 pre2 hp2
        (by omega)⟩
  have hsink := positive_one_two_owner_meet_only_at_sink x y z arms point ho ht
  rw [heq1] at hsink
  exact positive_labelOne_prefix_ne_sink x y z arms.2.1 pre1 hp1 hsink

theorem positive_two_zero_prefix_lists_disjoint (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    List.Disjoint
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega))
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega)) := by
  rw [List.disjoint_left]
  intro point htwo hzero
  obtain ⟨pre2, hp2, heq2⟩ :=
    (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) point).1 htwo
  obtain ⟨pre0, hp0, heq0⟩ :=
    (mem_labelZeroPrefixOwnerList_iff arms.1 (by omega) point).1 hzero
  have ht : PositiveLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point) := by
    right
    exact ⟨pre2, hp2, by
      rw [heq2]
      exact simplexPointToInt_labelTwoPrefixSimplexPoint arms.2.2 pre2 hp2
        (by omega)⟩
  have hz : PositiveLabelZeroPoint x y z arms.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre0, hp0, by
      rw [heq0]
      exact simplexPointToInt_labelZeroPrefixSimplexPoint arms.1 pre0 hp0
        (by omega)⟩
  have hsink := positive_two_zero_owner_meet_only_at_sink x y z arms point ht hz
  rw [heq2] at hsink
  exact positive_labelTwo_prefix_ne_sink x y z arms.2.2 pre2 hp2 hsink

theorem positive_prefix_lists_sink_disjoint (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega) ++
        labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega) ++
        labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega))
      [sinkPoint x y z] := by
  rw [List.disjoint_left]
  intro point hprefix hsink
  simp only [List.mem_append] at hprefix
  simp only [List.mem_singleton] at hsink
  subst point
  rcases hprefix with (hzero | hone) | htwo
  · obtain ⟨pre, hp, heq⟩ :=
      (mem_labelZeroPrefixOwnerList_iff arms.1 (by omega) _).1 hzero
    exact positive_labelZero_prefix_ne_sink x y z arms.1 pre hp heq.symm
  · obtain ⟨pre, hp, heq⟩ :=
      (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) _).1 hone
    exact positive_labelOne_prefix_ne_sink x y z arms.2.1 pre hp heq.symm
  · obtain ⟨pre, hp, heq⟩ :=
      (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) _).1 htwo
    exact positive_labelTwo_prefix_ne_sink x y z arms.2.2 pre hp heq.symm

theorem positiveYOwnerList_nodup (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYOwnerList x y z arms).Nodup := by
  have hzero := labelZeroPrefixOwnerList_nodup (t := x + y + z + 3)
    arms.1 (by omega)
  have hone := labelOnePrefixOwnerList_nodup (t := x + y + z + 3)
    arms.2.1 (by omega)
  have htwo := labelTwoPrefixOwnerList_nodup (t := x + y + z + 3)
    arms.2.2 (by omega)
  have h01 : List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega))
      (labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega)) :=
    positive_zero_one_prefix_lists_disjoint x y z arms
  have h02 : List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega))
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega)) :=
    (positive_two_zero_prefix_lists_disjoint x y z arms).symm
  have h12 := positive_one_two_prefix_lists_disjoint x y z arms
  have h01_2 : List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega) ++
        labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega))
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega)) := by
    rw [List.disjoint_append_left]
    exact ⟨h02, h12⟩
  have h01Nodup := List.Nodup.append hzero hone h01
  have hprefix := List.Nodup.append h01Nodup htwo h01_2
  exact List.Nodup.append hprefix (List.nodup_singleton _)
    (positive_prefix_lists_sink_disjoint x y z arms)

noncomputable def positiveYOwnerFinset (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    Finset (SimplexPoint (x + y + z + 3)) :=
  (positiveYOwnerList x y z arms).toFinset

theorem positiveYOwnerFinset_card (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYOwnerFinset x y z arms).card =
      3 * (x + y + z + 3) + 1 := by
  rw [positiveYOwnerFinset,
    List.toFinset_card_of_nodup (positiveYOwnerList_nodup x y z arms)]
  exact positiveYOwnerList_length x y z arms

theorem positiveYArmOwner_of_mem_ownerFinset (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (hmem : point ∈ positiveYOwnerFinset x y z arms) :
    PositiveYArmOwner x y z arms point := by
  simp only [positiveYOwnerFinset, List.mem_toFinset,
    positiveYOwnerList, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with ((hzero | hone) | htwo) | hsink
  · left
    obtain ⟨pre, hp, rfl⟩ :=
      (mem_labelZeroPrefixOwnerList_iff arms.1 (by omega) point).1 hzero
    right
    exact ⟨pre, hp, simplexPointToInt_labelZeroPrefixSimplexPoint
      arms.1 pre hp (by omega)⟩
  · right; left
    obtain ⟨pre, hp, rfl⟩ :=
      (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) point).1 hone
    right
    exact ⟨pre, hp, simplexPointToInt_labelOnePrefixSimplexPoint
      arms.2.1 pre hp (by omega)⟩
  · right; right
    obtain ⟨pre, hp, rfl⟩ :=
      (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) point).1 htwo
    right
    exact ⟨pre, hp, simplexPointToInt_labelTwoPrefixSimplexPoint
      arms.2.2 pre hp (by omega)⟩
  · subst point
    left
    left
    simp [simplexPointToInt, sinkPoint, intSink]

theorem positiveYStoneOwners_disjoint_ownerFinset (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    Disjoint (positiveYStoneOwners x y z arms)
      (positiveYOwnerFinset x y z arms) := by
  classical
  rw [Finset.disjoint_left]
  intro point hstone howner
  have hs := hstone
  simp [positiveYStoneOwners] at hs
  exact hs.2 (positiveYArmOwner_of_mem_ownerFinset x y z arms point howner)

theorem positiveYStoneOwners_card_bound (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYStoneOwners x y z arms).card +
        (3 * (x + y + z + 3) + 1) ≤
      Fintype.card (SimplexPoint (x + y + z + 3)) := by
  classical
  have hdisj := positiveYStoneOwners_disjoint_ownerFinset x y z arms
  have hsubset : positiveYStoneOwners x y z arms ∪
      positiveYOwnerFinset x y z arms ⊆ Finset.univ := Finset.subset_univ _
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisj,
    positiveYOwnerFinset_card] at hcard
  simpa using hcard

end BenzelProblem6Kernel
