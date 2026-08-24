import BenzelProblem6Kernel.RightmostExposedPlacement
import Mathlib.Data.List.Count

/-!
# Integer oriented chains of literal honeycomb edges

For every actual directed edge `e`, its coefficient is the number of forward
occurrences minus the number of occurrences of the exact reversed edge.  This
retains the orientation information discarded by the earlier XOR layer and is
fully executable.
-/

namespace BenzelProblem6Kernel

theorem lawful_count_eq_indicator_of_nodup
    {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha]
    (items : List Alpha) (hnodup : items.Nodup) (item : Alpha) :
    items.count item = if item ∈ items then 1 else 0 := by
  induction items with
  | nil => simp
  | cons head rest ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.count_cons, ih hnodup.2]
      by_cases hhead : head = item
      · subst head
        simp [hnodup.1]
      · simp [hhead, Ne.symm hhead]

theorem lawful_countP_eq_indicator_of_nodup
    {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha]
    (items : List Alpha) (hnodup : items.Nodup) (item : Alpha) :
    items.countP (fun candidate => candidate == item) =
      if item ∈ items then 1 else 0 := by
  rw [← List.count_eq_countP]
  exact lawful_count_eq_indicator_of_nodup items hnodup item

def directedEdgeCoefficient (edges : List LabeledHexEdge)
    (edge : LabeledHexEdge) : ℤ :=
  (edges.count edge : ℤ) - edges.count (reverseLabeledHexEdge edge)

def SameOrientedBoundaryChain
    (left right : List LabeledHexEdge) : Prop :=
  ∀ edge, directedEdgeCoefficient left edge =
    directedEdgeCoefficient right edge

theorem SameOrientedBoundaryChain.refl (edges : List LabeledHexEdge) :
    SameOrientedBoundaryChain edges edges := fun _ => rfl

theorem SameOrientedBoundaryChain.symm
    {left right : List LabeledHexEdge}
    (h : SameOrientedBoundaryChain left right) :
    SameOrientedBoundaryChain right left := fun edge => (h edge).symm

theorem SameOrientedBoundaryChain.trans
    {first second third : List LabeledHexEdge}
    (h₀ : SameOrientedBoundaryChain first second)
    (h₁ : SameOrientedBoundaryChain second third) :
    SameOrientedBoundaryChain first third :=
  fun edge => (h₀ edge).trans (h₁ edge)

theorem directedEdgeCoefficient_append
    (left right : List LabeledHexEdge) (edge : LabeledHexEdge) :
    directedEdgeCoefficient (left ++ right) edge =
      directedEdgeCoefficient left edge +
        directedEdgeCoefficient right edge := by
  simp [directedEdgeCoefficient, List.count_append]
  omega

theorem SameOrientedBoundaryChain.append
    {left₀ right₀ left₁ right₁ : List LabeledHexEdge}
    (h₀ : SameOrientedBoundaryChain left₀ right₀)
    (h₁ : SameOrientedBoundaryChain left₁ right₁) :
    SameOrientedBoundaryChain (left₀ ++ left₁) (right₀ ++ right₁) := by
  intro edge
  rw [directedEdgeCoefficient_append,
    directedEdgeCoefficient_append, h₀ edge, h₁ edge]

theorem reverseLabeledHexEdge_injective :
    Function.Injective reverseLabeledHexEdge := by
  intro left right h
  simpa [reverseLabeledHexEdge_involutive] using
    congrArg reverseLabeledHexEdge h

theorem directedEdgeCoefficient_reverse (edges : List LabeledHexEdge)
    (edge : LabeledHexEdge) :
    directedEdgeCoefficient
        (edges.reverse.map reverseLabeledHexEdge) edge =
      -directedEdgeCoefficient edges edge := by
  simp only [directedEdgeCoefficient, List.map_reverse,
    List.count_reverse]
  have hforward := List.count_map_of_injective edges
    reverseLabeledHexEdge reverseLabeledHexEdge_injective
      (reverseLabeledHexEdge edge)
  rw [reverseLabeledHexEdge_involutive] at hforward
  have hreverse := List.count_map_of_injective edges
    reverseLabeledHexEdge reverseLabeledHexEdge_injective edge
  rw [hforward, hreverse]
  ring

theorem SameOrientedBoundaryChain.perm
    {left right : List LabeledHexEdge} (hperm : List.Perm left right) :
    SameOrientedBoundaryChain left right := by
  intro edge
  simp only [directedEdgeCoefficient,
    hperm.count_eq edge,
    hperm.count_eq (reverseLabeledHexEdge edge)]

theorem translateLabeledHexEdge_injective (offset : HexVertex) :
    Function.Injective (translateLabeledHexEdge offset) := by
  intro left right h
  apply labeledHexEdge_ext
  · exact (translateHexVertexEmbedding offset).injective
      (congrArg LabeledHexEdge.source h)
  · exact (translateHexVertexEmbedding offset).injective
      (congrArg LabeledHexEdge.target h)
  · simpa [translateLabeledHexEdge] using
      congrArg LabeledHexEdge.label h

theorem translateLabeledHexEdge_reverse (offset : HexVertex)
    (edge : LabeledHexEdge) :
    translateLabeledHexEdge offset (reverseLabeledHexEdge edge) =
      reverseLabeledHexEdge (translateLabeledHexEdge offset edge) := by
  rfl

theorem SameOrientedBoundaryChain.translate
    {left right : List LabeledHexEdge}
    (hchain : SameOrientedBoundaryChain left right)
    (offset : HexVertex) :
    SameOrientedBoundaryChain
      (left.map (translateLabeledHexEdge offset))
      (right.map (translateLabeledHexEdge offset)) := by
  intro edge
  by_cases himage : ∃ source,
      translateLabeledHexEdge offset source = edge
  · obtain ⟨source, rfl⟩ := himage
    simp only [directedEdgeCoefficient,
      ← translateLabeledHexEdge_reverse,
      List.count_map_of_injective _ _
        (translateLabeledHexEdge_injective offset)]
    exact hchain source
  · have hnotForward : edge ∉
        left.map (translateLabeledHexEdge offset) ∧
        edge ∉ right.map (translateLabeledHexEdge offset) := by
      constructor <;> intro hmem <;>
        obtain ⟨source, _, hsource⟩ := List.mem_map.mp hmem <;>
        exact himage ⟨source, hsource⟩
    have hnotReverse : reverseLabeledHexEdge edge ∉
        left.map (translateLabeledHexEdge offset) ∧
        reverseLabeledHexEdge edge ∉
          right.map (translateLabeledHexEdge offset) := by
      constructor <;> intro hmem <;>
        obtain ⟨source, _, hsource⟩ := List.mem_map.mp hmem
      all_goals
        apply himage
        refine ⟨reverseLabeledHexEdge source, ?_⟩
        rw [translateLabeledHexEdge_reverse, hsource,
          reverseLabeledHexEdge_involutive]
    simp [directedEdgeCoefficient, List.count_eq_zero.mpr,
      hnotForward.1, hnotForward.2, hnotReverse.1, hnotReverse.2]

def orientedCellBoundaryList (cells : List Cell) :
    List LabeledHexEdge :=
  cells.flatMap labeledCellBoundary

def orientedPrototypeCellBoundaryList (tile : ProtoTile) (base : Cell) :
    List LabeledHexEdge :=
  orientedCellBoundaryList
    ((protoCells tile).map (translateLocalCell base))

end BenzelProblem6Kernel
