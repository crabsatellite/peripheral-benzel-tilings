import D4KernelOnly.GeneralClassMinusOneReduced
import D4KernelOnly.D4BoundarySpurReduction

/-! # Exact removal of the three class-minus-one geometric spurs -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def cmoCSpurEdge (s r : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (cmoStage3 s r) shadowC.neg .c
def cmoASpurEdge (s r : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (cmoStage7 s r) shadowA.neg .a
def cmoBSpurEdge (s r : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (cmoStage11 s r) shadowB.neg .b

def cmoStage2Last (s r : ℕ) : HexVertex :=
  walkPowerStart (cmoStage2 s r) (0, -3) (s - 1)
def cmoStage6Last (s r : ℕ) : HexVertex :=
  walkPowerStart (cmoStage6 s r) (3, 3) (s - 1)
def cmoStage10Last (s r : ℕ) : HexVertex :=
  walkPowerStart (cmoStage10 s r) (-3, 0) (s - 1)

theorem cmoBlock4_last_split (s r : ℕ) (hs : 1 ≤ s) :
    walkLabeledHexEdges (cmoStage2Last s r) d4LiteralStepBlock4 =
      walkLabeledHexEdges (cmoStage2Last s r) d4LiteralStepBlock4Core ++
        [reverseLabeledHexEdge (cmoCSpurEdge s r)] := by
  simp [d4LiteralStepBlock4, d4LiteralStepBlock4Core,
    cmoCSpurEdge, cmoStage2Last, walkPowerStart,
    walkLabeledHexEdges, cmoStage2, cmoStage3,
    reverseLabeledHexEdge, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals push_cast [Nat.cast_sub hs]
  all_goals ring
  all_goals simp

theorem cmoBlock2_last_split (s r : ℕ) (hs : 1 ≤ s) :
    walkLabeledHexEdges (cmoStage6Last s r) d4LiteralStepBlock2 =
      walkLabeledHexEdges (cmoStage6Last s r) d4LiteralStepBlock2Core ++
        [reverseLabeledHexEdge (cmoASpurEdge s r)] := by
  simp [d4LiteralStepBlock2, d4LiteralStepBlock2Core,
    cmoASpurEdge, cmoStage6Last, walkPowerStart,
    walkLabeledHexEdges, cmoStage6, cmoStage7,
    reverseLabeledHexEdge, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals push_cast [Nat.cast_sub hs]
  all_goals ring
  all_goals simp

theorem cmoBlock0_last_split (s r : ℕ) (hs : 1 ≤ s) :
    walkLabeledHexEdges (cmoStage10Last s r) d4LiteralStepBlock0 =
      walkLabeledHexEdges (cmoStage10Last s r) d4LiteralStepBlock0Core ++
        [reverseLabeledHexEdge (cmoBSpurEdge s r)] := by
  simp [d4LiteralStepBlock0, d4LiteralStepBlock0Core,
    cmoBSpurEdge, cmoStage10Last, walkPowerStart,
    walkLabeledHexEdges, cmoStage10, cmoStage11,
    reverseLabeledHexEdge, advanceLabeledHexEdge, addHexStep,
    shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals push_cast [Nat.cast_sub hs]
  all_goals ring
  all_goals simp

theorem cmoBlock4_power_split (s r : ℕ) (hs : 1 ≤ s) :
    walkLabeledHexEdges (cmoStage2 s r)
        (labeledStepWordPower d4LiteralStepBlock4 s) =
      walkLabeledHexEdges (cmoStage2 s r)
          (labeledStepWordPower d4LiteralStepBlock4 (s - 1)) ++
        walkLabeledHexEdges (cmoStage2Last s r) d4LiteralStepBlock4Core ++
        [reverseLabeledHexEdge (cmoCSpurEdge s r)] := by
  have hsEq : s = (s - 1) + 1 := by omega
  have hsplit : labeledStepWordPower d4LiteralStepBlock4 s =
      labeledStepWordPower d4LiteralStepBlock4 (s - 1) ++
        d4LiteralStepBlock4 := by
    conv_lhs => rw [hsEq]
    exact labeledStepWordPower_succ _ _
  rw [hsplit, walkLabeledHexEdges_append,
    generalLiteralBlock4_walkEnd_power]
  change _ ++ walkLabeledHexEdges (cmoStage2Last s r)
      d4LiteralStepBlock4 = _
  rw [cmoBlock4_last_split s r hs]
  simp [List.append_assoc]

theorem cmoBlock2_power_split (s r : ℕ) (hs : 1 ≤ s) :
    walkLabeledHexEdges (cmoStage6 s r)
        (labeledStepWordPower d4LiteralStepBlock2 s) =
      walkLabeledHexEdges (cmoStage6 s r)
          (labeledStepWordPower d4LiteralStepBlock2 (s - 1)) ++
        walkLabeledHexEdges (cmoStage6Last s r) d4LiteralStepBlock2Core ++
        [reverseLabeledHexEdge (cmoASpurEdge s r)] := by
  have hsEq : s = (s - 1) + 1 := by omega
  have hsplit : labeledStepWordPower d4LiteralStepBlock2 s =
      labeledStepWordPower d4LiteralStepBlock2 (s - 1) ++
        d4LiteralStepBlock2 := by
    conv_lhs => rw [hsEq]
    exact labeledStepWordPower_succ _ _
  rw [hsplit, walkLabeledHexEdges_append,
    generalLiteralBlock2_walkEnd_power]
  change _ ++ walkLabeledHexEdges (cmoStage6Last s r)
      d4LiteralStepBlock2 = _
  rw [cmoBlock2_last_split s r hs]
  simp [List.append_assoc]

theorem cmoBlock0_power_split (s r : ℕ) (hs : 1 ≤ s) :
    walkLabeledHexEdges (cmoStage10 s r)
        (labeledStepWordPower d4LiteralStepBlock0 s) =
      walkLabeledHexEdges (cmoStage10 s r)
          (labeledStepWordPower d4LiteralStepBlock0 (s - 1)) ++
        walkLabeledHexEdges (cmoStage10Last s r) d4LiteralStepBlock0Core ++
        [reverseLabeledHexEdge (cmoBSpurEdge s r)] := by
  have hsEq : s = (s - 1) + 1 := by omega
  have hsplit : labeledStepWordPower d4LiteralStepBlock0 s =
      labeledStepWordPower d4LiteralStepBlock0 (s - 1) ++
        d4LiteralStepBlock0 := by
    conv_lhs => rw [hsEq]
    exact labeledStepWordPower_succ _ _
  rw [hsplit, walkLabeledHexEdges_append,
    generalLiteralBlock0_walkEnd_power]
  change _ ++ walkLabeledHexEdges (cmoStage10Last s r)
      d4LiteralStepBlock0 = _
  rw [cmoBlock0_last_split s r hs]
  simp [List.append_assoc]

def cmoSpurlessSection0 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (cmoStage0 s r)
      (labeledStepWordPower d4LiteralStepBlock5 r) ++
    walkLabeledHexEdges (cmoStage1 s r) [(shadowC, .c)] ++
    walkLabeledHexEdges (cmoStage2 s r)
      (labeledStepWordPower d4LiteralStepBlock4 (s - 1)) ++
    walkLabeledHexEdges (cmoStage2Last s r) d4LiteralStepBlock4Core

def cmoSpurlessSection1 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (cmoStage4 s r)
      (labeledStepWordPower d4LiteralStepBlock3 r) ++
    walkLabeledHexEdges (cmoStage5 s r) [(shadowA, .a)] ++
    walkLabeledHexEdges (cmoStage6 s r)
      (labeledStepWordPower d4LiteralStepBlock2 (s - 1)) ++
    walkLabeledHexEdges (cmoStage6Last s r) d4LiteralStepBlock2Core

def cmoSpurlessSection2 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (cmoStage8 s r)
      (labeledStepWordPower d4LiteralStepBlock1 r) ++
    walkLabeledHexEdges (cmoStage9 s r) [(shadowB, .b)] ++
    walkLabeledHexEdges (cmoStage10 s r)
      (labeledStepWordPower d4LiteralStepBlock0 (s - 1)) ++
    walkLabeledHexEdges (cmoStage10Last s r) d4LiteralStepBlock0Core

def cmoSpurlessBoundaryWalk (s r : ℕ) : List LabeledHexEdge :=
  cmoSpurlessSection0 s r ++ cmoSpurlessSection1 s r ++
    cmoSpurlessSection2 s r

theorem classMinusOneBoundary_spur_decomposition
    (s r : ℕ) (hs : 1 ≤ s) :
    classMinusOneLiteralBoundaryWalk s r =
      cmoSpurlessSection0 s r ++
      [reverseLabeledHexEdge (cmoCSpurEdge s r), cmoCSpurEdge s r] ++
      cmoSpurlessSection1 s r ++
      [reverseLabeledHexEdge (cmoASpurEdge s r), cmoASpurEdge s r] ++
      cmoSpurlessSection2 s r ++
      [reverseLabeledHexEdge (cmoBSpurEdge s r), cmoBSpurEdge s r] := by
  rw [classMinusOneLiteralBoundaryWalk_eq_segments]
  simp [classMinusOneBoundaryWalkBySegments,
    cmoSpurlessSection0, cmoSpurlessSection1, cmoSpurlessSection2,
    cmoBlock4_power_split s r hs, cmoBlock2_power_split s r hs,
    cmoBlock0_power_split s r hs,
    cmoCSpurEdge, cmoASpurEdge, cmoBSpurEdge,
    walkLabeledHexEdges, List.append_assoc]

theorem cmoReducedBoundaryWalk_sublist_spurless
    (s r : ℕ) (hs : 1 ≤ s) :
    List.Sublist (cmoReducedBoundaryWalk s r)
      (cmoSpurlessBoundaryWalk s r) := by
  let section0 := cmoSpurlessSection0 s r
  let section1 := cmoSpurlessSection1 s r
  let section2 := cmoSpurlessSection2 s r
  let edgeC := reverseLabeledHexEdge (cmoCSpurEdge s r)
  let edgeA := reverseLabeledHexEdge (cmoASpurEdge s r)
  let edgeB := reverseLabeledHexEdge (cmoBSpurEdge s r)
  have hdecomp : classMinusOneLiteralBoundaryWalk s r =
      section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
      section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
      section2 ++ [edgeB, reverseLabeledHexEdge edgeB] := by
    simpa [section0, section1, section2, edgeC, edgeA, edgeB,
      reverseLabeledHexEdge_involutive] using
        classMinusOneBoundary_spur_decomposition s r hs
  have hnodup :
      (section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
       section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
       section2 ++ [edgeB, reverseLabeledHexEdge edgeB]).Nodup := by
    rw [← hdecomp]
    exact classMinusOneLiteralBoundaryWalk_nodup s r hs
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
  unfold cmoReducedBoundaryWalk
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
  simpa [cmoSpurlessBoundaryWalk, section0, section1, section2,
    List.append_assoc] using
      reduceGeometricBacktracks_sublist (section0 ++ section1 ++ section2)

theorem cmoSpurlessBoundary_length
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoSpurlessBoundaryWalk s r).length = 12 * (s + r) := by
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
        rw [labeledStepWordPower_succ, List.length_append, ih, Nat.succ_mul]
  simp only [cmoSpurlessBoundaryWalk, cmoSpurlessSection0,
    cmoSpurlessSection1, cmoSpurlessSection2,
    List.length_append, hwalk, hpower,
    d4LiteralStepBlock4Core, d4LiteralStepBlock2Core,
    d4LiteralStepBlock0Core, d4LiteralStepBlock5,
    d4LiteralStepBlock4, d4LiteralStepBlock3,
    d4LiteralStepBlock2, d4LiteralStepBlock1,
    d4LiteralStepBlock0,
    List.length_cons, List.length_nil]
  omega

theorem cmoReducedBoundary_length_le
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoReducedBoundaryWalk s r).length ≤ 12 * (s + r) := by
  rw [← cmoSpurlessBoundary_length s r hs]
  exact (cmoReducedBoundaryWalk_sublist_spurless s r hs).length_le

end FiniteDefects
