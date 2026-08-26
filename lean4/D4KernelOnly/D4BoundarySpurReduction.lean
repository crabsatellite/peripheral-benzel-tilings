import D4KernelOnly.D4BoundaryCellSideSupport

/-! # Exact removal of the three geometric boundary spurs -/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4LiteralStepBlock4Core : List D4LabeledStep :=
  [(shadowB.neg, .b), (shadowA, .a), (shadowB.neg, .b)]

def d4LiteralStepBlock2Core : List D4LabeledStep :=
  [(shadowC.neg, .c), (shadowB, .b), (shadowC.neg, .c)]

def d4LiteralStepBlock0Core : List D4LabeledStep :=
  [(shadowA.neg, .a), (shadowC, .c), (shadowA.neg, .a)]

def d4CSpurEdge (m : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (d4Stage3 m) shadowC.neg .c

def d4ASpurEdge (m : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (d4Stage7 m) shadowA.neg .a

def d4BSpurEdge (m : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (d4Stage11 m) shadowB.neg .b

theorem d4Block4_walk_split (m : ℕ) :
    walkLabeledHexEdges (d4Stage2 m) d4LiteralStepBlock4 =
      walkLabeledHexEdges (d4Stage2 m) d4LiteralStepBlock4Core ++
        [reverseLabeledHexEdge (d4CSpurEdge m)] := by
  simp [d4LiteralStepBlock4, d4LiteralStepBlock4Core,
    d4CSpurEdge, walkLabeledHexEdges, d4Stage2, d4Stage3,
    reverseLabeledHexEdge, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals ring
  all_goals simp

theorem d4Block2_walk_split (m : ℕ) :
    walkLabeledHexEdges (d4Stage6 m) d4LiteralStepBlock2 =
      walkLabeledHexEdges (d4Stage6 m) d4LiteralStepBlock2Core ++
        [reverseLabeledHexEdge (d4ASpurEdge m)] := by
  simp [d4LiteralStepBlock2, d4LiteralStepBlock2Core,
    d4ASpurEdge, walkLabeledHexEdges, d4Stage6, d4Stage7,
    reverseLabeledHexEdge, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals ring
  all_goals simp

theorem d4Block0_walk_split (m : ℕ) :
    walkLabeledHexEdges (d4Stage10 m) d4LiteralStepBlock0 =
      walkLabeledHexEdges (d4Stage10 m) d4LiteralStepBlock0Core ++
        [reverseLabeledHexEdge (d4BSpurEdge m)] := by
  simp [d4LiteralStepBlock0, d4LiteralStepBlock0Core,
    d4BSpurEdge, walkLabeledHexEdges, d4Stage10, d4Stage11,
    reverseLabeledHexEdge, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals ring

def d4SpurlessSection0 (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4Stage0 m)
      (labeledStepWordPower d4LiteralStepBlock5 (m + 1)) ++
    walkLabeledHexEdges (d4Stage1 m) [(shadowC, .c)] ++
    walkLabeledHexEdges (d4Stage2 m) d4LiteralStepBlock4Core

def d4SpurlessSection1 (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4Stage4 m)
      (labeledStepWordPower d4LiteralStepBlock3 (m + 1)) ++
    walkLabeledHexEdges (d4Stage5 m) [(shadowA, .a)] ++
    walkLabeledHexEdges (d4Stage6 m) d4LiteralStepBlock2Core

def d4SpurlessSection2 (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4Stage8 m)
      (labeledStepWordPower d4LiteralStepBlock1 (m + 1)) ++
    walkLabeledHexEdges (d4Stage9 m) [(shadowB, .b)] ++
    walkLabeledHexEdges (d4Stage10 m) d4LiteralStepBlock0Core

def d4SpurlessBoundaryWalk (m : ℕ) : List LabeledHexEdge :=
  d4SpurlessSection0 m ++ d4SpurlessSection1 m ++ d4SpurlessSection2 m

theorem d4LiteralBoundaryWalk_spur_decomposition (m : ℕ) :
    d4LiteralBoundaryWalk m =
      d4SpurlessSection0 m ++
      [reverseLabeledHexEdge (d4CSpurEdge m), d4CSpurEdge m] ++
      d4SpurlessSection1 m ++
      [reverseLabeledHexEdge (d4ASpurEdge m), d4ASpurEdge m] ++
      d4SpurlessSection2 m ++
      [reverseLabeledHexEdge (d4BSpurEdge m), d4BSpurEdge m] := by
  rw [d4LiteralBoundaryWalk_eq_segments]
  simp [d4LiteralBoundaryWalkBySegments, d4SpurlessSection0,
    d4SpurlessSection1, d4SpurlessSection2,
    d4Block4_walk_split, d4Block2_walk_split, d4Block0_walk_split,
    d4CSpurEdge, d4ASpurEdge, d4BSpurEdge,
    walkLabeledHexEdges, List.append_assoc]

theorem reduce_cons_reverse_pair
    (edge : LabeledHexEdge) (suffix : List LabeledHexEdge)
    (hnot : edge ∉ suffix) :
    reduceGeometricBacktracks
        (edge :: reverseLabeledHexEdge edge :: suffix) =
      reduceGeometricBacktracks suffix := by
  have hnotReduced : edge ∉ reduceGeometricBacktracks suffix := by
    intro hmem
    exact hnot ((reduceGeometricBacktracks_sublist suffix).subset hmem)
  simp only [reduceGeometricBacktracks]
  cases hreduced : reduceGeometricBacktracks suffix with
  | nil =>
      simp [prependReducedEdge, reverseLabeledHexEdge_involutive]
  | cons next rest =>
      have hne : edge ≠ next := by
        intro heq
        subst next
        exact hnotReduced (by simp [hreduced])
      simp [prependReducedEdge, hreduced, hne,
        reverseLabeledHexEdge_involutive]

theorem reduce_append_cons_reverse_pair
    (prefixEdges : List LabeledHexEdge) (edge : LabeledHexEdge)
    (suffix : List LabeledHexEdge) (hnot : edge ∉ suffix) :
    reduceGeometricBacktracks
        (prefixEdges ++ edge :: reverseLabeledHexEdge edge :: suffix) =
      reduceGeometricBacktracks (prefixEdges ++ suffix) := by
  induction prefixEdges with
  | nil => exact reduce_cons_reverse_pair edge suffix hnot
  | cons head tail ih =>
      simp only [List.cons_append, reduceGeometricBacktracks]
      rw [ih]

theorem nodup_pair_edge_not_suffix
    (prefixEdges : List LabeledHexEdge) (edge : LabeledHexEdge)
    (suffix : List LabeledHexEdge)
    (hnodup :
      (prefixEdges ++ edge :: reverseLabeledHexEdge edge :: suffix).Nodup) :
    edge ∉ suffix := by
  have htail : (edge :: reverseLabeledHexEdge edge :: suffix).Nodup :=
    hnodup.sublist (List.sublist_append_right prefixEdges _)
  exact fun hmem => (List.nodup_cons.mp htail).1 (by simp [hmem])

theorem d4ReducedBoundaryWalk_sublist_spurless (m : ℕ) :
    List.Sublist (d4ReducedBoundaryWalk m) (d4SpurlessBoundaryWalk m) := by
  let section0 := d4SpurlessSection0 m
  let section1 := d4SpurlessSection1 m
  let section2 := d4SpurlessSection2 m
  let edgeC := reverseLabeledHexEdge (d4CSpurEdge m)
  let edgeA := reverseLabeledHexEdge (d4ASpurEdge m)
  let edgeB := reverseLabeledHexEdge (d4BSpurEdge m)
  have hdecomp : d4LiteralBoundaryWalk m =
      section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
      section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
      section2 ++ [edgeB, reverseLabeledHexEdge edgeB] := by
    simpa [section0, section1, section2, edgeC, edgeA, edgeB,
      reverseLabeledHexEdge_involutive] using
        d4LiteralBoundaryWalk_spur_decomposition m
  have hnodup :
      (section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
       section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
       section2 ++ [edgeB, reverseLabeledHexEdge edgeB]).Nodup := by
    rw [← hdecomp]
    exact d4LiteralBoundaryWalk_nodup m
  have hnotC : edgeC ∉
      section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
      section2 ++ [edgeB, reverseLabeledHexEdge edgeB] := by
    apply nodup_pair_edge_not_suffix section0 edgeC
    simpa [List.append_assoc] using hnodup
  have hnotA : edgeA ∉ section2 ++ [edgeB, reverseLabeledHexEdge edgeB] := by
    let prefixEdges :=
      section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++ section1
    apply nodup_pair_edge_not_suffix prefixEdges edgeA
    simpa [prefixEdges, List.append_assoc] using hnodup
  have hnotB : edgeB ∉ ([] : List LabeledHexEdge) := by simp
  unfold d4ReducedBoundaryWalk
  rw [hdecomp]
  let suffixC := section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
    section2 ++ [edgeB, reverseLabeledHexEdge edgeB]
  let suffixA := section2 ++ [edgeB, reverseLabeledHexEdge edgeB]
  rw [show section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
      section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
      section2 ++ [edgeB, reverseLabeledHexEdge edgeB] =
      section0 ++ edgeC :: reverseLabeledHexEdge edgeC :: suffixC by
    simp [suffixC, List.append_assoc]]
  rw [reduce_append_cons_reverse_pair section0 edgeC
    suffixC (by simpa [suffixC] using hnotC)]
  rw [show section0 ++ suffixC =
      (section0 ++ section1) ++
        edgeA :: reverseLabeledHexEdge edgeA :: suffixA by
    simp [suffixC, suffixA, List.append_assoc]]
  rw [reduce_append_cons_reverse_pair (section0 ++ section1) edgeA
    suffixA (by simpa [suffixA] using hnotA)]
  rw [show section0 ++ section1 ++ suffixA =
      (section0 ++ section1 ++ section2) ++
        edgeB :: reverseLabeledHexEdge edgeB :: [] by
    simp [suffixA, List.append_assoc]]
  rw [reduce_append_cons_reverse_pair
    (section0 ++ section1 ++ section2) edgeB [] hnotB]
  simpa [d4SpurlessBoundaryWalk, section0, section1, section2,
    List.append_assoc] using
      reduceGeometricBacktracks_sublist (section0 ++ section1 ++ section2)

theorem d4SpurlessBoundary_length (m : ℕ) :
    (d4SpurlessBoundaryWalk m).length = 12 * m + 24 := by
  have hwalk (source : HexVertex) (steps : List D4LabeledStep) :
      (walkLabeledHexEdges source steps).length = steps.length := by
    induction steps generalizing source with
    | nil => rfl
    | cons step rest ih =>
        simp only [walkLabeledHexEdges, List.length_cons]
        change (walkLabeledHexEdges (addHexStep source step.1) rest).length + 1 =
          rest.length + 1
        rw [ih]
  have hpower (word : List D4LabeledStep) (exponent : ℕ) :
      (labeledStepWordPower word exponent).length = exponent * word.length := by
    induction exponent with
    | zero => simp
    | succ exponent ih =>
        rw [labeledStepWordPower_succ, List.length_append, ih,
          Nat.succ_mul]
  simp only [d4SpurlessBoundaryWalk, d4SpurlessSection0,
    d4SpurlessSection1, d4SpurlessSection2,
    List.length_append, hwalk, hpower,
    d4LiteralStepBlock4Core, d4LiteralStepBlock2Core,
    d4LiteralStepBlock0Core, d4LiteralStepBlock5,
    d4LiteralStepBlock3, d4LiteralStepBlock1,
    List.length_cons, List.length_nil]
  omega

theorem d4ReducedBoundary_length_le (m : ℕ) :
    (d4ReducedBoundaryWalk m).length ≤ 12 * m + 24 := by
  rw [← d4SpurlessBoundary_length m]
  exact (d4ReducedBoundaryWalk_sublist_spurless m).length_le

end FiniteDefects
