import BenzelProblem6Kernel.NegativeYCoverExistence
import BenzelProblem6Kernel.PositiveYOwnerCount

/-!
# Counting the owners occupied by a reconstructed negative Y
-/

namespace BenzelProblem6Kernel

theorem negative_labelZero_prefix_ne_sink (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    labelZeroPrefixSimplexPoint (t := x + y + z + 3)
      path pre hp (by omega) ≠ sinkPoint x y z := by
  intro heq
  have hbound := negative_labelZero_prefix_bounds x y z path pre hp
  have hw := labelZeroPrefixSimplexPoint_w (t := x + y + z + 3)
    path pre hp (by omega)
  have heqw := congrArg SimplexPoint.w heq
  simp [sinkPoint] at heqw
  have hw' :
      ((labelZeroPrefixSimplexPoint (t := x + y + z + 3)
        path pre hp (by omega)).w : ℤ) =
        (labelZeroPrefixPoint (x + y + z + 3) pre).w := hw
  omega

theorem negative_labelOne_prefix_ne_sink (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    labelOnePrefixSimplexPoint (t := x + y + z + 3)
      path pre hp (by omega) ≠ sinkPoint x y z := by
  intro heq
  have hbound := negative_labelOne_prefix_bounds x y z path pre hp
  have hu := labelOnePrefixSimplexPoint_u (t := x + y + z + 3)
    path pre hp (by omega)
  have hequ := congrArg SimplexPoint.u heq
  simp [sinkPoint] at hequ
  have hu' :
      ((labelOnePrefixSimplexPoint (t := x + y + z + 3)
        path pre hp (by omega)).u : ℤ) =
        (labelOnePrefixPoint (x + y + z + 3) pre).u := hu
  omega

theorem negative_labelTwo_prefix_ne_sink (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path) :
    labelTwoPrefixSimplexPoint (t := x + y + z + 3)
      path pre hp (by omega) ≠ sinkPoint x y z := by
  intro heq
  have hbound := negative_labelTwo_prefix_bounds x y z path pre hp
  have hv := labelTwoPrefixSimplexPoint_v (t := x + y + z + 3)
    path pre hp (by omega)
  have heqv := congrArg SimplexPoint.v heq
  simp [sinkPoint] at heqv
  have hv' :
      ((labelTwoPrefixSimplexPoint (t := x + y + z + 3)
        path pre hp (by omega)).v : ℤ) =
        (labelTwoPrefixPoint (x + y + z + 3) pre).v := hv
  omega

noncomputable def negativeYOwnerList (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    List (SimplexPoint (x + y + z + 3)) :=
  labelZeroPrefixOwnerList arms.1 (by omega) ++
    labelOnePrefixOwnerList arms.2.1 (by omega) ++
    labelTwoPrefixOwnerList arms.2.2 (by omega) ++
    [sinkPoint x y z]

@[simp] theorem negativeYOwnerList_length (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYOwnerList x y z arms).length =
      3 * (x + y + z + 3) + 1 := by
  simp [negativeYOwnerList]
  omega

theorem negative_zero_one_prefix_lists_disjoint (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega))
      (labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega)) := by
  rw [List.disjoint_left]
  intro point hzero hone
  obtain ⟨pre0, hp0, heq0⟩ :=
    (mem_labelZeroPrefixOwnerList_iff arms.1 (by omega) point).1 hzero
  obtain ⟨pre1, hp1, heq1⟩ :=
    (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) point).1 hone
  have hz : NegativeLabelZeroPoint x y z arms.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre0, hp0, by
      rw [heq0]
      exact simplexPointToInt_labelZeroPrefixSimplexPoint arms.1 pre0 hp0
        (by omega)⟩
  have ho : NegativeLabelOnePoint x y z arms.2.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre1, hp1, by
      rw [heq1]
      exact simplexPointToInt_labelOnePrefixSimplexPoint arms.2.1 pre1 hp1
        (by omega)⟩
  have hsink := negative_zero_one_owner_meet_only_at_sink x y z arms point hz ho
  rw [heq0] at hsink
  exact negative_labelZero_prefix_ne_sink x y z arms.1 pre0 hp0 hsink

theorem negative_one_two_prefix_lists_disjoint (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    List.Disjoint
      (labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega))
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega)) := by
  rw [List.disjoint_left]
  intro point hone htwo
  obtain ⟨pre1, hp1, heq1⟩ :=
    (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) point).1 hone
  obtain ⟨pre2, hp2, heq2⟩ :=
    (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) point).1 htwo
  have ho : NegativeLabelOnePoint x y z arms.2.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre1, hp1, by
      rw [heq1]
      exact simplexPointToInt_labelOnePrefixSimplexPoint arms.2.1 pre1 hp1
        (by omega)⟩
  have ht : NegativeLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point) := by
    right
    exact ⟨pre2, hp2, by
      rw [heq2]
      exact simplexPointToInt_labelTwoPrefixSimplexPoint arms.2.2 pre2 hp2
        (by omega)⟩
  have hsink := negative_one_two_owner_meet_only_at_sink x y z arms point ho ht
  rw [heq1] at hsink
  exact negative_labelOne_prefix_ne_sink x y z arms.2.1 pre1 hp1 hsink

theorem negative_two_zero_prefix_lists_disjoint (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    List.Disjoint
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega))
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega)) := by
  rw [List.disjoint_left]
  intro point htwo hzero
  obtain ⟨pre2, hp2, heq2⟩ :=
    (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) point).1 htwo
  obtain ⟨pre0, hp0, heq0⟩ :=
    (mem_labelZeroPrefixOwnerList_iff arms.1 (by omega) point).1 hzero
  have ht : NegativeLabelTwoPoint x y z arms.2.2
      (simplexPointToInt point) := by
    right
    exact ⟨pre2, hp2, by
      rw [heq2]
      exact simplexPointToInt_labelTwoPrefixSimplexPoint arms.2.2 pre2 hp2
        (by omega)⟩
  have hz : NegativeLabelZeroPoint x y z arms.1
      (simplexPointToInt point) := by
    right
    exact ⟨pre0, hp0, by
      rw [heq0]
      exact simplexPointToInt_labelZeroPrefixSimplexPoint arms.1 pre0 hp0
        (by omega)⟩
  have hsink := negative_two_zero_owner_meet_only_at_sink x y z arms point ht hz
  rw [heq2] at hsink
  exact negative_labelTwo_prefix_ne_sink x y z arms.2.2 pre2 hp2 hsink

theorem negative_prefix_lists_sink_disjoint (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
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
    exact negative_labelZero_prefix_ne_sink x y z arms.1 pre hp heq.symm
  · obtain ⟨pre, hp, heq⟩ :=
      (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) _).1 hone
    exact negative_labelOne_prefix_ne_sink x y z arms.2.1 pre hp heq.symm
  · obtain ⟨pre, hp, heq⟩ :=
      (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) _).1 htwo
    exact negative_labelTwo_prefix_ne_sink x y z arms.2.2 pre hp heq.symm

theorem negativeYOwnerList_nodup (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYOwnerList x y z arms).Nodup := by
  have hzero := labelZeroPrefixOwnerList_nodup (t := x + y + z + 3)
    arms.1 (by omega)
  have hone := labelOnePrefixOwnerList_nodup (t := x + y + z + 3)
    arms.2.1 (by omega)
  have htwo := labelTwoPrefixOwnerList_nodup (t := x + y + z + 3)
    arms.2.2 (by omega)
  have h01 : List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega))
      (labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega)) :=
    negative_zero_one_prefix_lists_disjoint x y z arms
  have h02 : List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega))
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega)) :=
    (negative_two_zero_prefix_lists_disjoint x y z arms).symm
  have h12 := negative_one_two_prefix_lists_disjoint x y z arms
  have h01_2 : List.Disjoint
      (labelZeroPrefixOwnerList (t := x + y + z + 3) arms.1 (by omega) ++
        labelOnePrefixOwnerList (t := x + y + z + 3) arms.2.1 (by omega))
      (labelTwoPrefixOwnerList (t := x + y + z + 3) arms.2.2 (by omega)) := by
    rw [List.disjoint_append_left]
    exact ⟨h02, h12⟩
  have h01Nodup := List.Nodup.append hzero hone h01
  have hprefix := List.Nodup.append h01Nodup htwo h01_2
  exact List.Nodup.append hprefix (List.nodup_singleton _)
    (negative_prefix_lists_sink_disjoint x y z arms)

noncomputable def negativeYOwnerFinset (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    Finset (SimplexPoint (x + y + z + 3)) :=
  (negativeYOwnerList x y z arms).toFinset

theorem negativeYOwnerFinset_card (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYOwnerFinset x y z arms).card =
      3 * (x + y + z + 3) + 1 := by
  rw [negativeYOwnerFinset,
    List.toFinset_card_of_nodup (negativeYOwnerList_nodup x y z arms)]
  exact negativeYOwnerList_length x y z arms

theorem negativeYArmOwner_of_mem_ownerFinset (x y z : ℕ)
    (arms : NegativeArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (hmem : point ∈ negativeYOwnerFinset x y z arms) :
    NegativeYArmOwner x y z arms point := by
  simp only [negativeYOwnerFinset, List.mem_toFinset,
    negativeYOwnerList, List.mem_append, List.mem_singleton] at hmem
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

theorem negativeYStoneOwners_disjoint_ownerFinset (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    Disjoint (negativeYStoneOwners x y z arms)
      (negativeYOwnerFinset x y z arms) := by
  classical
  rw [Finset.disjoint_left]
  intro point hstone howner
  have hs := hstone
  simp [negativeYStoneOwners] at hs
  exact hs.2 (negativeYArmOwner_of_mem_ownerFinset x y z arms point howner)

theorem negativeYStoneOwners_card_bound (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYStoneOwners x y z arms).card +
        (3 * (x + y + z + 3) + 1) ≤
      Fintype.card (SimplexPoint (x + y + z + 3)) := by
  classical
  have hdisj := negativeYStoneOwners_disjoint_ownerFinset x y z arms
  have hsubset : negativeYStoneOwners x y z arms ∪
      negativeYOwnerFinset x y z arms ⊆ Finset.univ := Finset.subset_univ _
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisj,
    negativeYOwnerFinset_card] at hcard
  simpa using hcard

end BenzelProblem6Kernel
