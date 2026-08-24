import BenzelProblem6Kernel.LabeledBoundaryCancellation

/-!
# Translation equivariance of labeled honeycomb boundaries
-/

namespace BenzelProblem6Kernel

def translateCell (offset cell : Cell) : Cell :=
  (offset.1 + cell.1, offset.2 + cell.2)

def hexVertexTranslation (offset : Cell) : HexVertex :=
  (offset.1 + 2 * offset.2, -offset.1 + offset.2)

def translateHexVertex (offset : HexVertex) (vertex : HexVertex) : HexVertex :=
  (offset.1 + vertex.1, offset.2 + vertex.2)

def translateHexVertexEmbedding (offset : HexVertex) : HexVertex ↪ HexVertex where
  toFun := translateHexVertex offset
  inj' := by
    intro left right h
    apply Prod.ext <;> have := congrArg Prod.fst h <;>
      have := congrArg Prod.snd h <;>
      simp [translateHexVertex] at * <;> omega

def translateLabeledHexEdge (offset : HexVertex)
    (edge : LabeledHexEdge) : LabeledHexEdge :=
  ⟨translateHexVertex offset edge.source,
    translateHexVertex offset edge.target, edge.label⟩

def translateLabeledHexEdgeKeyEmbedding (offset : HexVertex) :
    LabeledHexEdgeKey ↪ LabeledHexEdgeKey where
  toFun key :=
    (Sym2.map (translateHexVertex offset) key.1, key.2)
  inj' := by
    intro left right h
    have hedge := congrArg Prod.fst h
    have hlabel := congrArg Prod.snd h
    apply Prod.ext
    · exact Sym2.map.injective
        (translateHexVertexEmbedding offset).injective hedge
    · exact hlabel

theorem hexCellCenter_translate (offset cell : Cell) :
    hexCellCenter (translateCell offset cell) =
      translateHexVertex (hexVertexTranslation offset) (hexCellCenter cell) := by
  apply Prod.ext <;> simp [hexCellCenter, translateCell,
    translateHexVertex, hexVertexTranslation] <;> ring

theorem addHexStep_translate (offset vertex : HexVertex) (step : ShadowStep) :
    addHexStep (translateHexVertex offset vertex) step =
      translateHexVertex offset (addHexStep vertex step) := by
  apply Prod.ext <;> simp [addHexStep, translateHexVertex] <;> ring

theorem advanceLabeledHexEdge_translate (offset source : HexVertex)
    (step : ShadowStep) (label : ShadowLabel) :
    advanceLabeledHexEdge (translateHexVertex offset source) step label =
      translateLabeledHexEdge offset
        (advanceLabeledHexEdge source step label) := by
  apply labeledHexEdge_ext
  · rfl
  · exact addHexStep_translate offset source step
  · rfl

theorem walkLabeledHexEdges_translate (offset source : HexVertex)
    (steps : List LabeledHexStep) :
    walkLabeledHexEdges (translateHexVertex offset source) steps =
      (walkLabeledHexEdges source steps).map
        (translateLabeledHexEdge offset) := by
  induction steps generalizing source with
  | nil => rfl
  | cons step rest ih =>
      simp only [walkLabeledHexEdges, List.map_cons,
        advanceLabeledHexEdge_translate]
      congr 1
      exact ih _

theorem hexCellStartVertex_translate (offset cell : Cell) :
    hexCellStartVertex (translateCell offset cell) =
      translateHexVertex (hexVertexTranslation offset)
        (hexCellStartVertex cell) := by
  rw [hexCellStartVertex, hexCellCenter_translate,
    addHexStep_translate]
  rfl

theorem labeledCellBoundary_translate (offset cell : Cell) :
    labeledCellBoundary (translateCell offset cell) =
      (labeledCellBoundary cell).map
        (translateLabeledHexEdge (hexVertexTranslation offset)) := by
  rw [labeledCellBoundary, hexCellStartVertex_translate,
    walkLabeledHexEdges_translate]
  rfl

theorem prototypeBoundaryStart_translate
    (tile : ProtoTile) (offset base : Cell) :
    prototypeBoundaryStart tile (translateCell offset base) =
      translateHexVertex (hexVertexTranslation offset)
        (prototypeBoundaryStart tile base) := by
  cases tile <;>
    apply Prod.ext <;>
    simp [prototypeBoundaryStart, hexCellCenter_translate,
      translateHexVertex] <;> ring

theorem literalPrototypeBoundary_translate
    (tile : ProtoTile) (offset base : Cell) :
    literalPrototypeBoundary tile (translateCell offset base) =
      (literalPrototypeBoundary tile base).map
        (translateLabeledHexEdge (hexVertexTranslation offset)) := by
  rw [literalPrototypeBoundary, prototypeBoundaryStart_translate,
    walkLabeledHexEdges_translate]
  rfl

theorem translateLabeledHexEdge_key (offset : HexVertex)
    (edge : LabeledHexEdge) :
    (translateLabeledHexEdge offset edge).key =
      translateLabeledHexEdgeKeyEmbedding offset edge.key := by
  simp [LabeledHexEdge.key, translateLabeledHexEdge,
    translateLabeledHexEdgeKeyEmbedding]

theorem labeledBoundaryKeys_translate (offset : HexVertex)
    (edges : List LabeledHexEdge) :
    labeledBoundaryKeys (edges.map (translateLabeledHexEdge offset)) =
      (labeledBoundaryKeys edges).map
        (translateLabeledHexEdgeKeyEmbedding offset) := by
  classical
  ext key
  simp [labeledBoundaryKeys, translateLabeledHexEdge_key]

theorem cellBoundaryKeys_translate (offset cell : Cell) :
    cellBoundaryKeys (translateCell offset cell) =
      (cellBoundaryKeys cell).map
        (translateLabeledHexEdgeKeyEmbedding (hexVertexTranslation offset)) := by
  rw [cellBoundaryKeys, labeledCellBoundary_translate,
    labeledBoundaryKeys_translate]
  rfl

theorem finsetMap_symmDiff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (embedding : α ↪ β) (left right : Finset α) :
    (symmDiff left right).map embedding =
      symmDiff (left.map embedding) (right.map embedding) := by
  ext item
  simp [Finset.mem_symmDiff]
  aesop

theorem xorCellBoundaryList_translate (offset : Cell) (cells : List Cell) :
    xorCellBoundaryList (cells.map (translateCell offset)) =
      (xorCellBoundaryList cells).map
        (translateLabeledHexEdgeKeyEmbedding (hexVertexTranslation offset)) := by
  induction cells with
  | nil => simp [xorCellBoundaryList]
  | cons cell rest ih =>
      simp only [List.map_cons, xorCellBoundaryList,
        cellBoundaryKeys_translate, ih]
      rw [← finsetMap_symmDiff]

theorem translateLocalCell_eq_translateCell (base : Cell) (cell : LocalCell) :
    translateLocalCell base cell =
      translateCell base (translateLocalCell (0, 0) cell) := by
  apply Prod.ext <;>
    simp [translateLocalCell, translateCell]

theorem prototypeCells_translate (tile : ProtoTile) (base : Cell) :
    (protoCells tile).map (translateLocalCell base) =
      ((protoCells tile).map (translateLocalCell (0, 0))).map
        (translateCell base) := by
  simp only [List.map_map, Function.comp_apply]
  apply List.map_congr_left
  intro cell hcell
  exact translateLocalCell_eq_translateCell base cell

theorem prototypeCellBoundaryXor_translate (tile : ProtoTile) (base : Cell) :
    prototypeCellBoundaryXor tile base =
      (prototypeCellBoundaryXor tile (0, 0)).map
        (translateLabeledHexEdgeKeyEmbedding (hexVertexTranslation base)) := by
  rw [prototypeCellBoundaryXor, prototypeCellBoundaryXor,
    prototypeCells_translate, xorCellBoundaryList_translate]

theorem prototypeOuterBoundaryKeys_translate (tile : ProtoTile) (base : Cell) :
    prototypeOuterBoundaryKeys tile base =
      (prototypeOuterBoundaryKeys tile (0, 0)).map
        (translateLabeledHexEdgeKeyEmbedding (hexVertexTranslation base)) := by
  rw [prototypeOuterBoundaryKeys, prototypeOuterBoundaryKeys]
  have hbase : base = translateCell base (0, 0) := by
    apply Prod.ext <;> simp [translateCell]
  calc
    labeledBoundaryKeys (literalPrototypeBoundary tile base) =
        labeledBoundaryKeys
          (literalPrototypeBoundary tile (translateCell base (0, 0))) := by
      rw [← hbase]
    _ = _ := by
      rw [literalPrototypeBoundary_translate,
        labeledBoundaryKeys_translate]

end BenzelProblem6Kernel
