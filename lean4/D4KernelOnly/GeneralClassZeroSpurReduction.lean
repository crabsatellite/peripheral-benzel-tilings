import D4KernelOnly.GeneralClassZeroReducedPerimeter
import D4KernelOnly.D4BoundarySpurReduction

/-! # Exact removal of the three class-zero geometric spurs -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

def czBlock5Core : List LabeledHexStep :=
  [(shadowB, .b), (shadowA.neg, .a), (shadowB, .b)]
def czBlock4Tail : List LabeledHexStep :=
  [(shadowA.neg, .a), (shadowB, .b), (shadowA.neg, .a)]
def czBlock3Core : List LabeledHexStep :=
  [(shadowC, .c), (shadowB.neg, .b), (shadowC, .c)]
def czBlock2Tail : List LabeledHexStep :=
  [(shadowB.neg, .b), (shadowC, .c), (shadowB.neg, .b)]
def czBlock1Core : List LabeledHexStep :=
  [(shadowA, .a), (shadowC.neg, .c), (shadowA, .a)]
def czBlock0Tail : List LabeledHexStep :=
  [(shadowC.neg, .c), (shadowA, .a), (shadowC.neg, .c)]

theorem czBlock5_split : czLiteralBlock5 = czBlock5Core ++ [(shadowC.neg, .c)] := by decide
theorem czBlock4_split : czLiteralBlock4 = (shadowC, .c) :: czBlock4Tail := by decide
theorem czBlock3_split : czLiteralBlock3 = czBlock3Core ++ [(shadowA.neg, .a)] := by decide
theorem czBlock2_split : czLiteralBlock2 = (shadowA, .a) :: czBlock2Tail := by decide
theorem czBlock1_split : czLiteralBlock1 = czBlock1Core ++ [(shadowB.neg, .b)] := by decide
theorem czBlock0_split : czLiteralBlock0 = (shadowB, .b) :: czBlock0Tail := by decide

theorem labeledHexStepWordPower_split_last
    (word : List LabeledHexStep) (n : ℕ) (hn : 1 ≤ n) :
    labeledHexStepWordPower word n =
      labeledHexStepWordPower word (n - 1) ++ word := by
  have hnEq : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hnEq]
  exact labeledHexStepWordPower_succ word (n - 1)

theorem labeledHexStepWordPower_split_first
    (word : List LabeledHexStep) (n : ℕ) (hn : 1 ≤ n) :
    labeledHexStepWordPower word n =
      word ++ labeledHexStepWordPower word (n - 1) := by
  rw [labeledHexStepWordPower_split_last word n hn]
  exact (labeledHexStepWordPower_commute word (n - 1)).symm

theorem czBlock5_power_spur_split (r : ℕ) (hr : 1 ≤ r) :
    labeledHexStepWordPower czLiteralBlock5 r =
      labeledHexStepWordPower czLiteralBlock5 (r - 1) ++
        czBlock5Core ++ [(shadowC.neg, .c)] := by
  rw [labeledHexStepWordPower_split_last _ r hr]
  conv_lhs => rhs; rw [czBlock5_split]
  simp [List.append_assoc]

theorem czBlock4_power_spur_split (s : ℕ) (hs : 1 ≤ s) :
    labeledHexStepWordPower czLiteralBlock4 s =
      (shadowC, .c) :: czBlock4Tail ++
        labeledHexStepWordPower czLiteralBlock4 (s - 1) := by
  rw [labeledHexStepWordPower_split_first _ s hs]
  conv_lhs => lhs; rw [czBlock4_split]

theorem czBlock3_power_spur_split (r : ℕ) (hr : 1 ≤ r) :
    labeledHexStepWordPower czLiteralBlock3 r =
      labeledHexStepWordPower czLiteralBlock3 (r - 1) ++
        czBlock3Core ++ [(shadowA.neg, .a)] := by
  rw [labeledHexStepWordPower_split_last _ r hr]
  conv_lhs => rhs; rw [czBlock3_split]
  simp [List.append_assoc]

theorem czBlock2_power_spur_split (s : ℕ) (hs : 1 ≤ s) :
    labeledHexStepWordPower czLiteralBlock2 s =
      (shadowA, .a) :: czBlock2Tail ++
        labeledHexStepWordPower czLiteralBlock2 (s - 1) := by
  rw [labeledHexStepWordPower_split_first _ s hs]
  conv_lhs => lhs; rw [czBlock2_split]

theorem czBlock1_power_spur_split (r : ℕ) (hr : 1 ≤ r) :
    labeledHexStepWordPower czLiteralBlock1 r =
      labeledHexStepWordPower czLiteralBlock1 (r - 1) ++
        czBlock1Core ++ [(shadowB.neg, .b)] := by
  rw [labeledHexStepWordPower_split_last _ r hr]
  conv_lhs => rhs; rw [czBlock1_split]
  simp [List.append_assoc]

theorem czBlock0_power_spur_split (s : ℕ) (hs : 1 ≤ s) :
    labeledHexStepWordPower czLiteralBlock0 s =
      (shadowB, .b) :: czBlock0Tail ++
        labeledHexStepWordPower czLiteralBlock0 (s - 1) := by
  rw [labeledHexStepWordPower_split_first _ s hs]
  conv_lhs => lhs; rw [czBlock0_split]

def czPreCSteps (s r : ℕ) : List LabeledHexStep :=
  labeledHexStepWordPower czLiteralBlock5 (r - 1) ++ czBlock5Core

def czBetweenCASteps (s r : ℕ) : List LabeledHexStep :=
  czBlock4Tail ++ labeledHexStepWordPower czLiteralBlock4 (s - 1) ++
    labeledHexStepWordPower czLiteralBlock3 (r - 1) ++ czBlock3Core

def czBetweenABSteps (s r : ℕ) : List LabeledHexStep :=
  czBlock2Tail ++ labeledHexStepWordPower czLiteralBlock2 (s - 1) ++
    labeledHexStepWordPower czLiteralBlock1 (r - 1) ++ czBlock1Core

def czAfterBSteps (s r : ℕ) : List LabeledHexStep :=
  czBlock0Tail ++ labeledHexStepWordPower czLiteralBlock0 (s - 1)

theorem classZeroBoundarySteps_spur_decomposition
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    classZeroLiteralBoundarySteps s r =
      czPreCSteps s r ++ [(shadowC.neg, .c), (shadowC, .c)] ++
      czBetweenCASteps s r ++ [(shadowA.neg, .a), (shadowA, .a)] ++
      czBetweenABSteps s r ++ [(shadowB.neg, .b), (shadowB, .b)] ++
      czAfterBSteps s r := by
  rw [classZeroLiteralBoundarySteps_eq_explicit]
  unfold classZeroLiteralBoundaryStepsExplicit
  rw [czBlock5_power_spur_split r hr,
    czBlock4_power_spur_split s hs,
    czBlock3_power_spur_split r hr,
    czBlock2_power_spur_split s hs,
    czBlock1_power_spur_split r hr,
    czBlock0_power_spur_split s hs]
  simp [czPreCSteps, czBetweenCASteps, czBetweenABSteps,
    czAfterBSteps, List.append_assoc]

def czSpurSourceC (s r : ℕ) : HexVertex :=
  labeledHexWalkEnd (classZeroClockwiseRoot s r) (czPreCSteps s r)
def czSpurEdgeC (s r : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (czSpurSourceC s r) shadowC.neg .c
def czSection0Edges (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (classZeroClockwiseRoot s r) (czPreCSteps s r)

def czSpurSourceA (s r : ℕ) : HexVertex :=
  labeledHexWalkEnd (czSpurSourceC s r) (czBetweenCASteps s r)
def czSpurEdgeA (s r : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (czSpurSourceA s r) shadowA.neg .a
def czSection1Edges (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (czSpurSourceC s r) (czBetweenCASteps s r)

def czSpurSourceB (s r : ℕ) : HexVertex :=
  labeledHexWalkEnd (czSpurSourceA s r) (czBetweenABSteps s r)
def czSpurEdgeB (s r : ℕ) : LabeledHexEdge :=
  advanceLabeledHexEdge (czSpurSourceB s r) shadowB.neg .b
def czSection2Edges (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (czSpurSourceA s r) (czBetweenABSteps s r)
def czSection3Edges (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (czSpurSourceB s r) (czAfterBSteps s r)

def czSpurlessBoundaryWalk (s r : ℕ) : List LabeledHexEdge :=
  czSection0Edges s r ++ czSection1Edges s r ++
    czSection2Edges s r ++ czSection3Edges s r

theorem walk_spur_pair_C (source : HexVertex) :
    walkLabeledHexEdges source [(shadowC.neg, .c), (shadowC, .c)] =
      [advanceLabeledHexEdge source shadowC.neg .c,
        reverseLabeledHexEdge (advanceLabeledHexEdge source shadowC.neg .c)] := by
  rcases source with ⟨x, y⟩
  simp [walkLabeledHexEdges, reverseLabeledHexEdge,
    advanceLabeledHexEdge, addHexStep, shadowC, ShadowStep.neg]

theorem walk_spur_pair_A (source : HexVertex) :
    walkLabeledHexEdges source [(shadowA.neg, .a), (shadowA, .a)] =
      [advanceLabeledHexEdge source shadowA.neg .a,
        reverseLabeledHexEdge (advanceLabeledHexEdge source shadowA.neg .a)] := by
  rcases source with ⟨x, y⟩
  simp [walkLabeledHexEdges, reverseLabeledHexEdge,
    advanceLabeledHexEdge, addHexStep, shadowA, ShadowStep.neg]

theorem walk_spur_pair_B (source : HexVertex) :
    walkLabeledHexEdges source [(shadowB.neg, .b), (shadowB, .b)] =
      [advanceLabeledHexEdge source shadowB.neg .b,
        reverseLabeledHexEdge (advanceLabeledHexEdge source shadowB.neg .b)] := by
  rcases source with ⟨x, y⟩
  simp [walkLabeledHexEdges, reverseLabeledHexEdge,
    advanceLabeledHexEdge, addHexStep, shadowB, ShadowStep.neg]

theorem walkEnd_spur_pair_C (source : HexVertex) :
    labeledHexWalkEnd source [(shadowC.neg, .c), (shadowC, .c)] = source := by
  rcases source with ⟨x, y⟩
  simp [labeledHexWalkEnd, addHexStep, shadowC, ShadowStep.neg]
theorem walkEnd_spur_pair_A (source : HexVertex) :
    labeledHexWalkEnd source [(shadowA.neg, .a), (shadowA, .a)] = source := by
  rcases source with ⟨x, y⟩
  simp [labeledHexWalkEnd, addHexStep, shadowA, ShadowStep.neg]
theorem walkEnd_spur_pair_B (source : HexVertex) :
    labeledHexWalkEnd source [(shadowB.neg, .b), (shadowB, .b)] = source := by
  rcases source with ⟨x, y⟩
  simp [labeledHexWalkEnd, addHexStep, shadowB, ShadowStep.neg]

theorem classZeroBoundary_spur_decomposition
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    classZeroLiteralBoundaryWalk s r =
      czSection0Edges s r ++ [czSpurEdgeC s r,
        reverseLabeledHexEdge (czSpurEdgeC s r)] ++
      czSection1Edges s r ++ [czSpurEdgeA s r,
        reverseLabeledHexEdge (czSpurEdgeA s r)] ++
      czSection2Edges s r ++ [czSpurEdgeB s r,
        reverseLabeledHexEdge (czSpurEdgeB s r)] ++
      czSection3Edges s r := by
  rw [classZeroLiteralBoundaryWalk,
    classZeroBoundarySteps_spur_decomposition s r hs hr]
  simp only [walkLabeledHexEdges_append, labeledHexWalkEnd_append]
  rw [walk_spur_pair_C, walkEnd_spur_pair_C,
    walk_spur_pair_A, walkEnd_spur_pair_A,
    walk_spur_pair_B, walkEnd_spur_pair_B]
  rfl

theorem czReducedBoundary_sublist_spurless
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    List.Sublist (czReducedBoundaryWalk s r) (czSpurlessBoundaryWalk s r) := by
  let section0 := czSection0Edges s r
  let section1 := czSection1Edges s r
  let section2 := czSection2Edges s r
  let section3 := czSection3Edges s r
  let edgeC := czSpurEdgeC s r
  let edgeA := czSpurEdgeA s r
  let edgeB := czSpurEdgeB s r
  have hdecomp : classZeroLiteralBoundaryWalk s r =
      section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
      section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
      section2 ++ [edgeB, reverseLabeledHexEdge edgeB] ++ section3 := by
    simpa [section0, section1, section2, section3, edgeC, edgeA, edgeB]
      using classZeroBoundary_spur_decomposition s r hs hr
  have hnodup :
      (section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
       section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
       section2 ++ [edgeB, reverseLabeledHexEdge edgeB] ++ section3).Nodup := by
    rw [← hdecomp]
    exact classZeroLiteralBoundaryWalk_nodup s r
  have hnotC : edgeC ∉ section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
      section2 ++ [edgeB, reverseLabeledHexEdge edgeB] ++ section3 := by
    apply nodup_pair_edge_not_suffix section0 edgeC
    simpa [List.append_assoc] using hnodup
  have hnotA : edgeA ∉ section2 ++ [edgeB, reverseLabeledHexEdge edgeB] ++
      section3 := by
    let prefixEdges := section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++ section1
    apply nodup_pair_edge_not_suffix prefixEdges edgeA
    simpa [prefixEdges, List.append_assoc] using hnodup
  have hnotB : edgeB ∉ section3 := by
    let prefixEdges := section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
      section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++ section2
    apply nodup_pair_edge_not_suffix prefixEdges edgeB
    simpa [prefixEdges, List.append_assoc] using hnodup
  unfold czReducedBoundaryWalk
  rw [hdecomp]
  let suffixC := section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
    section2 ++ [edgeB, reverseLabeledHexEdge edgeB] ++ section3
  let suffixA := section2 ++ [edgeB, reverseLabeledHexEdge edgeB] ++ section3
  rw [show section0 ++ [edgeC, reverseLabeledHexEdge edgeC] ++
      section1 ++ [edgeA, reverseLabeledHexEdge edgeA] ++
      section2 ++ [edgeB, reverseLabeledHexEdge edgeB] ++ section3 =
      section0 ++ edgeC :: reverseLabeledHexEdge edgeC :: suffixC by
        simp [suffixC, List.append_assoc]]
  rw [reduce_append_cons_reverse_pair section0 edgeC suffixC
    (by simpa [suffixC] using hnotC)]
  rw [show section0 ++ suffixC = (section0 ++ section1) ++
      edgeA :: reverseLabeledHexEdge edgeA :: suffixA by
        simp [suffixC, suffixA, List.append_assoc]]
  rw [reduce_append_cons_reverse_pair (section0 ++ section1) edgeA suffixA
    (by simpa [suffixA] using hnotA)]
  rw [show section0 ++ section1 ++ suffixA =
      (section0 ++ section1 ++ section2) ++
        edgeB :: reverseLabeledHexEdge edgeB :: section3 by
        simp [suffixA, List.append_assoc]]
  rw [reduce_append_cons_reverse_pair
    (section0 ++ section1 ++ section2) edgeB section3 hnotB]
  simpa [czSpurlessBoundaryWalk, section0, section1, section2, section3,
    List.append_assoc] using reduceGeometricBacktracks_sublist
      (section0 ++ section1 ++ section2 ++ section3)

theorem walkLabeledHexEdges_length
    (source : HexVertex) (steps : List LabeledHexStep) :
    (walkLabeledHexEdges source steps).length = steps.length := by
  induction steps generalizing source with
  | nil => rfl
  | cons step rest ih =>
      simp only [walkLabeledHexEdges, List.length_cons]
      change (walkLabeledHexEdges (addHexStep source step.1) rest).length + 1 =
        rest.length + 1
      rw [ih]

theorem classZeroLiteralBoundaryWalk_length (s r : ℕ) :
    (classZeroLiteralBoundaryWalk s r).length = 12 * (s + r) := by
  rw [classZeroLiteralBoundaryWalk, walkLabeledHexEdges_length]
  unfold classZeroLiteralBoundarySteps classZeroClockwiseSteps
  have hpower (word : List LabeledHexStep) (n : ℕ) :
      (labeledHexStepWordPower word n).length = n * word.length := by
    rw [labeledHexStepWordPower_eq_labeledStepWordPower]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [labeledStepWordPower_succ, List.length_append, ih, Nat.succ_mul]
  simp [List.length_flatMap, hpower,
    literalPeripheralBlock₀, literalPeripheralBlock₁,
    literalPeripheralBlock₂, literalPeripheralBlock₃,
    literalPeripheralBlock₄, literalPeripheralBlock₅] <;> omega

theorem czSpurlessBoundary_length
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (czSpurlessBoundaryWalk s r).length = 12 * (s + r) - 6 := by
  have hlen := congrArg List.length (classZeroBoundary_spur_decomposition s r hs hr)
  rw [classZeroLiteralBoundaryWalk_length] at hlen
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  simp [czSpurlessBoundaryWalk]
  omega

theorem czReducedBoundary_length_upper
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (czReducedBoundaryWalk s r).length ≤ 12 * (s + r) - 6 := by
  rw [← czSpurlessBoundary_length s r hs hr]
  exact (czReducedBoundary_sublist_spurless s r hs hr).length_le

theorem czReducedBoundary_length
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (czReducedBoundaryWalk s r).length = 12 * (s + r) - 6 :=
  Nat.le_antisymm (czReducedBoundary_length_upper s r hs hr)
    (czReducedBoundary_length_lower s r hs hr)

theorem czPerimeterEdges_perm_reduced
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (czPerimeterEdges s r).Perm (czReducedBoundaryWalk s r) := by
  have hsubset : (czPerimeterEdges s r).toFinset ⊆
      (czReducedBoundaryWalk s r).toFinset := by
    intro edge hedge
    exact List.mem_toFinset.mpr
      (czPerimeterEdges_subset_reduced s r hs hr edge
        (List.mem_toFinset.mp hedge))
  have hcard : (czReducedBoundaryWalk s r).toFinset.card ≤
      (czPerimeterEdges s r).toFinset.card := by
    rw [List.toFinset_card_of_nodup (czReducedBoundary_nodup s r),
      List.toFinset_card_of_nodup (czPerimeterEdges_nodup s r),
      czReducedBoundary_length s r hs hr,
      czPerimeterEdges_length s r hs hr]
  have hfinset := Finset.eq_of_subset_of_card_le hsubset hcard
  apply (List.perm_ext_iff_of_nodup
    (czPerimeterEdges_nodup s r) (czReducedBoundary_nodup s r)).mpr
  intro edge
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp hfinset edge

end FiniteDefects
