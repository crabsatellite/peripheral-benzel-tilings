import BenzelProblem6Kernel.BenzelHexVertex
import BenzelProblem6Kernel.OrientedPlacementBoundaryCancellation

/-! # Local vertex decomposition of literal trihexes -/

namespace BenzelProblem6Kernel

def edgeSourceFinset (edges : List LabeledHexEdge) : Finset HexVertex :=
  (edges.map LabeledHexEdge.source).toFinset

def prototypeCellVertexFinset (tile : ProtoTile) (base : Cell) :
    Finset HexVertex :=
  edgeSourceFinset (orientedPrototypeCellBoundaryList tile base)

def prototypeBoundaryVertexFinset (tile : ProtoTile) (base : Cell) :
    Finset HexVertex :=
  edgeSourceFinset (literalPrototypeBoundary tile base)

def placementCellVertexFinset {m : ℕ}
    (placement : LiteralPlacement m) : Finset HexVertex :=
  prototypeCellVertexFinset placement.tile placement.base

def placementBoundaryVertexFinset {m : ℕ}
    (placement : LiteralPlacement m) : Finset HexVertex :=
  prototypeBoundaryVertexFinset placement.tile placement.base

theorem edgeSourceFinset_translate (offset : HexVertex)
    (edges : List LabeledHexEdge) :
    edgeSourceFinset (edges.map (translateLabeledHexEdge offset)) =
      (edgeSourceFinset edges).map (translateHexVertexEmbedding offset) := by
  ext vertex
  simp [edgeSourceFinset, translateLabeledHexEdge,
    translateHexVertexEmbedding]

theorem prototypeCellVertexFinset_translate
    (tile : ProtoTile) (base : Cell) :
    prototypeCellVertexFinset tile base =
      (prototypeCellVertexFinset tile (0, 0)).map
        (translateHexVertexEmbedding (hexVertexTranslation base)) := by
  calc
    prototypeCellVertexFinset tile base =
        edgeSourceFinset
          ((orientedPrototypeCellBoundaryList tile (0, 0)).map
            (translateLabeledHexEdge (hexVertexTranslation base))) := by
      exact congrArg edgeSourceFinset
        (orientedPrototypeCellBoundaryList_translate tile base)
    _ = (prototypeCellVertexFinset tile (0, 0)).map
          (translateHexVertexEmbedding (hexVertexTranslation base)) := by
      rw [edgeSourceFinset_translate, prototypeCellVertexFinset]

theorem prototypeBoundaryVertexFinset_translate
    (tile : ProtoTile) (base : Cell) :
    prototypeBoundaryVertexFinset tile base =
      (prototypeBoundaryVertexFinset tile (0, 0)).map
        (translateHexVertexEmbedding (hexVertexTranslation base)) := by
  have hbase : base = translateCell base (0, 0) := by
    rcases base with ⟨i, j⟩
    simp [translateCell]
  calc
    prototypeBoundaryVertexFinset tile base =
        prototypeBoundaryVertexFinset tile
          (translateCell base (0, 0)) := congrArg _ hbase
    _ =
        edgeSourceFinset
          ((literalPrototypeBoundary tile (0, 0)).map
            (translateLabeledHexEdge (hexVertexTranslation base))) := by
      exact congrArg edgeSourceFinset
        (literalPrototypeBoundary_translate tile base (0, 0))
    _ = (prototypeBoundaryVertexFinset tile (0, 0)).map
          (translateHexVertexEmbedding (hexVertexTranslation base)) := by
      rw [edgeSourceFinset_translate, prototypeBoundaryVertexFinset]

theorem upHexVertex_translate_zero (base : Cell) :
    upHexVertex base =
      translateHexVertex (hexVertexTranslation base)
        (upHexVertex (0, 0)) := by
  rcases base with ⟨i, j⟩
  apply Prod.ext <;>
    simp [upHexVertex, translateHexVertex, hexVertexTranslation]

theorem canonical_stone_vertex_decomposition :
    prototypeCellVertexFinset .stone (0, 0) =
      prototypeBoundaryVertexFinset .stone (0, 0) ∪
        {upHexVertex (0, 0)} := by
  decide

theorem canonical_stone_center_not_boundary :
    upHexVertex (0, 0) ∉
      prototypeBoundaryVertexFinset .stone (0, 0) := by
  decide

theorem canonical_boneA_vertex_decomposition :
    prototypeCellVertexFinset .boneA (0, 0) =
      prototypeBoundaryVertexFinset .boneA (0, 0) := by
  decide

theorem canonical_boneB_vertex_decomposition :
    prototypeCellVertexFinset .boneB (0, 0) =
      prototypeBoundaryVertexFinset .boneB (0, 0) := by
  decide

theorem canonical_boneC_vertex_decomposition :
    prototypeCellVertexFinset .boneC (0, 0) =
      prototypeBoundaryVertexFinset .boneC (0, 0) := by
  decide

theorem prototype_vertex_decomposition (tile : ProtoTile) (base : Cell) :
    prototypeCellVertexFinset tile base =
      prototypeBoundaryVertexFinset tile base ∪
        if tile = .stone then {upHexVertex base} else ∅ := by
  rw [prototypeCellVertexFinset_translate,
    prototypeBoundaryVertexFinset_translate]
  cases tile
  · rw [if_pos rfl, canonical_stone_vertex_decomposition,
      Finset.map_union, Finset.map_singleton]
    have hu :
        (translateHexVertexEmbedding (hexVertexTranslation base))
            (upHexVertex (0, 0)) =
          upHexVertex base := by
      change translateHexVertex (hexVertexTranslation base)
          (upHexVertex (0, 0)) = _
      exact (upHexVertex_translate_zero base).symm
    rw [hu]
  · rw [if_neg (by decide), canonical_boneA_vertex_decomposition]
    simp
  · rw [if_neg (by decide), canonical_boneB_vertex_decomposition]
    simp
  · rw [if_neg (by decide), canonical_boneC_vertex_decomposition]
    simp

theorem placement_vertex_decomposition {m : ℕ}
    (placement : LiteralPlacement m) :
    placementCellVertexFinset placement =
      placementBoundaryVertexFinset placement ∪
        if placement.tile = .stone then
          {upHexVertex placement.base} else ∅ :=
  prototype_vertex_decomposition placement.tile placement.base

theorem stone_center_not_boundary (base : Cell) :
    upHexVertex base ∉ prototypeBoundaryVertexFinset .stone base := by
  rw [prototypeBoundaryVertexFinset_translate]
  intro hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨vertex, hvertex, htranslated⟩ := hmem
  have hvertexEq : vertex = upHexVertex (0, 0) := by
    apply (translateHexVertexEmbedding
      (hexVertexTranslation base)).injective
    rw [htranslated]
    change upHexVertex base =
      translateHexVertex (hexVertexTranslation base)
        (upHexVertex (0, 0))
    exact upHexVertex_translate_zero base
  subst vertex
  exact canonical_stone_center_not_boundary hvertex

theorem stonePlacement_center_not_boundary {m : ℕ}
    (placement : LiteralPlacement m) (hstone : placement.tile = .stone) :
    upHexVertex placement.base ∉ placementBoundaryVertexFinset placement := by
  rw [placementBoundaryVertexFinset, hstone]
  exact stone_center_not_boundary placement.base

end BenzelProblem6Kernel
