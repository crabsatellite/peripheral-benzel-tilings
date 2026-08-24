import BenzelProblem6Kernel.PeripheralBoundaryIdentity

/-!
# The literal peripheral benzel boundary walk

The six blocks below are the reflected physical class-zero boundary blocks in
the repository's `(i,j)` coordinates.  Their start vertex is the reflected
rightmost augmented corner.  The listed walk is clockwise; reversing its
oriented edges gives the counterclockwise literal boundary word used by the
Conway--Lagarias invariant.
-/

namespace BenzelProblem6Kernel

def labeledHexStepWordPower (word : List LabeledHexStep) :
    ℕ → List LabeledHexStep
  | 0 => []
  | exponent + 1 => labeledHexStepWordPower word exponent ++ word

@[simp] theorem labeledHexStepWordPower_zero
    (word : List LabeledHexStep) :
    labeledHexStepWordPower word 0 = [] := rfl

@[simp] theorem labeledHexStepWordPower_succ
    (word : List LabeledHexStep) (exponent : ℕ) :
    labeledHexStepWordPower word (exponent + 1) =
      labeledHexStepWordPower word exponent ++ word := rfl

theorem labeledHexStepWordPower_labels
    (word : List LabeledHexStep) (exponent : ℕ) :
    (labeledHexStepWordPower word exponent).map Prod.snd =
      shadowLabelWordPower (word.map Prod.snd) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledHexStepWordPower_succ,
        shadowLabelWordPower_succ, List.map_append, ih]

theorem shadowLabelWordPower_map_mirror
    (word : List ShadowLabel) (exponent : ℕ) :
    shadowLabelWordPower (word.map mirrorShadowLabel) exponent =
      (shadowLabelWordPower word exponent).map mirrorShadowLabel := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [shadowLabelWordPower_succ, shadowLabelWordPower_succ,
        List.map_append, ih]

def literalPeripheralBlock₀ : List LabeledHexStep :=
  [(shadowC, .c), (shadowA.neg, .a),
    (shadowC, .c), (shadowB.neg, .b)]

def literalPeripheralBlock₁ : List LabeledHexStep :=
  [(shadowB, .b), (shadowA.neg, .a),
    (shadowC, .c), (shadowA.neg, .a)]

def literalPeripheralBlock₂ : List LabeledHexStep :=
  [(shadowB, .b), (shadowC.neg, .c),
    (shadowB, .b), (shadowA.neg, .a)]

def literalPeripheralBlock₃ : List LabeledHexStep :=
  [(shadowA, .a), (shadowC.neg, .c),
    (shadowB, .b), (shadowC.neg, .c)]

def literalPeripheralBlock₄ : List LabeledHexStep :=
  [(shadowA, .a), (shadowB.neg, .b),
    (shadowA, .a), (shadowC.neg, .c)]

def literalPeripheralBlock₅ : List LabeledHexStep :=
  [(shadowC, .c), (shadowB.neg, .b),
    (shadowA, .a), (shadowB.neg, .b)]

theorem literalPeripheralBlock₀_labels :
    literalPeripheralBlock₀.map Prod.snd =
      classZeroBoundaryBlock₀.map mirrorShadowLabel := by decide

theorem literalPeripheralBlock₁_labels :
    literalPeripheralBlock₁.map Prod.snd =
      classZeroBoundaryBlock₁.map mirrorShadowLabel := by decide

theorem literalPeripheralBlock₂_labels :
    literalPeripheralBlock₂.map Prod.snd =
      classZeroBoundaryBlock₂.map mirrorShadowLabel := by decide

theorem literalPeripheralBlock₃_labels :
    literalPeripheralBlock₃.map Prod.snd =
      classZeroBoundaryBlock₃.map mirrorShadowLabel := by decide

theorem literalPeripheralBlock₄_labels :
    literalPeripheralBlock₄.map Prod.snd =
      classZeroBoundaryBlock₄.map mirrorShadowLabel := by decide

theorem literalPeripheralBlock₅_labels :
    literalPeripheralBlock₅.map Prod.snd =
      classZeroBoundaryBlock₅.map mirrorShadowLabel := by decide

def literalPeripheralClockwiseSteps (m : ℕ) : List LabeledHexStep :=
  labeledHexStepWordPower literalPeripheralBlock₀ 1 ++
  labeledHexStepWordPower literalPeripheralBlock₁ (m + 3) ++
  labeledHexStepWordPower literalPeripheralBlock₂ 1 ++
  labeledHexStepWordPower literalPeripheralBlock₃ (m + 3) ++
  labeledHexStepWordPower literalPeripheralBlock₄ 1 ++
  labeledHexStepWordPower literalPeripheralBlock₅ (m + 3)

def literalPeripheralClockwiseStart (m : ℕ) : HexVertex :=
  ((m : ℤ) + 5, -((m : ℤ) + 2))

def literalPeripheralClockwiseBoundary (m : ℕ) :
    List LabeledHexEdge :=
  walkLabeledHexEdges (literalPeripheralClockwiseStart m)
    (literalPeripheralClockwiseSteps m)

theorem literalPeripheralClockwiseSteps_labels (m : ℕ) :
    (literalPeripheralClockwiseSteps m).map Prod.snd =
      (classZeroBoundaryLabels 1 (m + 3)).map mirrorShadowLabel := by
  simp only [literalPeripheralClockwiseSteps, classZeroBoundaryLabels,
    List.map_append, labeledHexStepWordPower_labels,
    literalPeripheralBlock₀_labels, literalPeripheralBlock₁_labels,
    literalPeripheralBlock₂_labels, literalPeripheralBlock₃_labels,
    literalPeripheralBlock₄_labels, literalPeripheralBlock₅_labels,
    List.map_map, shadowLabelWordPower_map_mirror]

theorem literalPeripheralClockwiseBoundary_word (m : ℕ) :
    labeledEdgeWord (literalPeripheralClockwiseBoundary m) =
      (classZeroBoundaryLabels 1 (m + 3)).map mirrorShadowLabel := by
  rw [literalPeripheralClockwiseBoundary, labeledEdgeWord_walk,
    literalPeripheralClockwiseSteps_labels]

def reverseLabeledHexEdge (edge : LabeledHexEdge) : LabeledHexEdge :=
  ⟨edge.target, edge.source, edge.label⟩

@[simp] theorem reverseLabeledHexEdge_label (edge : LabeledHexEdge) :
    (reverseLabeledHexEdge edge).label = edge.label := rfl

theorem reverseLabeledHexEdge_key (edge : LabeledHexEdge) :
    (reverseLabeledHexEdge edge).key = edge.key := by
  apply Prod.ext
  · exact Sym2.eq_swap
  · rfl

def literalPeripheralBoundary (m : ℕ) : List LabeledHexEdge :=
  (literalPeripheralClockwiseBoundary m).reverse.map reverseLabeledHexEdge

theorem labeledEdgeWord_reverseEdges (edges : List LabeledHexEdge) :
    labeledEdgeWord (edges.reverse.map reverseLabeledHexEdge) =
      (labeledEdgeWord edges).reverse := by
  simp [labeledEdgeWord, List.map_map]

theorem literalPeripheralBoundary_word (m : ℕ) :
    labeledEdgeWord (literalPeripheralBoundary m) =
      literalPeripheralBoundaryLabels m := by
  rw [literalPeripheralBoundary, labeledEdgeWord_reverseEdges,
    literalPeripheralClockwiseBoundary_word]
  rfl

theorem labeledBoundaryKeys_reverseEdges (edges : List LabeledHexEdge) :
    labeledBoundaryKeys (edges.reverse.map reverseLabeledHexEdge) =
      labeledBoundaryKeys edges := by
  ext key
  simp only [labeledBoundaryKeys, Finset.mem_image, List.mem_toFinset,
    List.mem_map, List.mem_reverse]
  constructor
  · rintro ⟨reversedEdge, ⟨edge, hedge, rfl⟩, hkey⟩
    exact ⟨edge, hedge, (reverseLabeledHexEdge_key edge).symm.trans hkey⟩
  · rintro ⟨edge, hedge, hkey⟩
    exact ⟨reverseLabeledHexEdge edge, ⟨edge, hedge, rfl⟩,
      (reverseLabeledHexEdge_key edge).trans hkey⟩

theorem literalPeripheralBoundary_keys (m : ℕ) :
    labeledBoundaryKeys (literalPeripheralBoundary m) =
      labeledBoundaryKeys (literalPeripheralClockwiseBoundary m) := by
  exact labeledBoundaryKeys_reverseEdges _

end BenzelProblem6Kernel
