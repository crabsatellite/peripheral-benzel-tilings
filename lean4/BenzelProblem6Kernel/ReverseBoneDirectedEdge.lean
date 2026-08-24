import BenzelProblem6Kernel.LiteralPathDataUniqueness

/-!
# A reconstructed bone as its explicit literal directed edge
-/

namespace BenzelProblem6Kernel

theorem GoodBoneClass.tile_ne_stone (boneClass : GoodBoneClass) :
    boneClass.tile ≠ .stone := by
  rcases boneClass <;> decide

theorem reverseBoneBase_residue {t : ℕ} (source : SimplexPoint t)
    (boneClass : GoodBoneClass) :
    placementBaseResidue t (reverseBoneBase source boneClass) =
      boneClass.residue := by
  have hphase := owner_anchor_is_phase source
  rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphase
  have hdiv : (3 : ℤ) ∣ ownerQ source - ownerR source - (t : ℤ) := by
    obtain ⟨k, hk⟩ := hphase
    exact ⟨-k, by omega⟩
  obtain ⟨k, hk⟩ := hdiv
  have hzero : (3 * k) % 3 = 0 := Int.mul_emod_right 3 k
  have hminusOne : (3 * k - 1) % 3 = 2 := by
    rw [Int.sub_emod, hzero]
    norm_num
  have hplusOne : (3 * k + 1) % 3 = 1 := by
    rw [Int.add_emod, hzero]
    norm_num
  have hminusThree : (3 * k - 3) % 3 = 0 := by
    rw [Int.sub_emod, hzero]
    norm_num
  rcases boneClass <;>
    simp [reverseBoneBase, GoodBoneClass.sourceShift,
      GoodBoneClass.residue, placementBaseResidue, residueOfInt,
      ownerQ, ownerR] at hk ⊢ <;>
    first
    | rw [show (source.w : ℤ) - source.u - ((source.u : ℤ) - source.v) - t =
        3 * k by omega]
    | rw [show (source.w : ℤ) - source.u - 1 - ((source.u : ℤ) - source.v) - t =
        3 * k - 1 by omega]
    | rw [show (source.w : ℤ) - source.u - ((source.u : ℤ) - source.v - 1) - t =
        3 * k + 1 by omega]
    | rw [show (source.w : ℤ) - source.u - 1 - ((source.u : ℤ) - source.v + 2) - t =
        3 * k - 3 by omega]
    | rw [show (source.w : ℤ) - source.u - ((source.u : ℤ) - source.v + 1) - t =
        3 * k - 1 by omega]
  all_goals simp_all [hzero, hminusOne, hplusOne, hminusThree]

theorem reverseBonePlacement_isClass {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) :
    IsPlacementClass
      (reverseBonePlacement source target boneClass hstep
        hsourceMem htargetMem) boneClass := by
  constructor
  · rfl
  · exact reverseBoneBase_residue source boneClass

noncomputable def reverseBoneDirectedEdge {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) : LiteralDirectedEdge m where
  placement := reverseBonePlacement source target boneClass hstep
    hsourceMem htargetMem
  boneClass := boneClass
  class_spec := reverseBonePlacement_isClass source target boneClass hstep
    hsourceMem htargetMem
  source := source
  target := target
  source_anchor := by
    have h := reverseBoneBase_source_anchor source boneClass
    exact ⟨congrArg Prod.fst h |>.symm, congrArg Prod.snd h |>.symm⟩
  target_anchor := by
    have h := reverseBoneBase_target_anchor source target boneClass hstep
    exact ⟨congrArg Prod.fst h |>.symm, congrArg Prod.snd h |>.symm⟩

@[simp] theorem reverseBoneDirectedEdge_placement {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) :
    (reverseBoneDirectedEdge source target boneClass hstep
      hsourceMem htargetMem).placement =
      reverseBonePlacement source target boneClass hstep
        hsourceMem htargetMem := rfl

@[simp] theorem reverseBoneDirectedEdge_source {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) :
    (reverseBoneDirectedEdge source target boneClass hstep
      hsourceMem htargetMem).source = source := rfl

@[simp] theorem reverseBoneDirectedEdge_target {m : ℕ}
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label)) :
    (reverseBoneDirectedEdge source target boneClass hstep
      hsourceMem htargetMem).target = target := rfl

noncomputable def reverseBoneEdgeOfTiling
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1) : LiteralDirectedEdge m :=
  directedEdgeOfBoneMember hstone tiling
    ⟨reverseBonePlacement source target boneClass hstep hsourceMem htargetMem,
      by
        simp only [bonePlacementFinset, Finset.mem_filter]
        exact ⟨hplacement, boneClass.tile_ne_stone⟩⟩

theorem reverseBoneEdgeOfTiling_mem
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1) :
    reverseBoneEdgeOfTiling hstone tiling source target boneClass hstep
      hsourceMem htargetMem hplacement ∈ literalDirectedEdges hstone tiling := by
  exact directedEdgeOfBoneMember_mem hstone tiling _

@[simp] theorem reverseBoneEdgeOfTiling_placement
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1) :
    (reverseBoneEdgeOfTiling hstone tiling source target boneClass hstep
      hsourceMem htargetMem hplacement).placement =
      reverseBonePlacement source target boneClass hstep
        hsourceMem htargetMem := rfl

theorem reverseBoneEdgeOfTiling_class
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1) :
    (reverseBoneEdgeOfTiling hstone tiling source target boneClass hstep
      hsourceMem htargetMem hplacement).boneClass = boneClass := by
  let placement := reverseBonePlacement source target boneClass hstep
    hsourceMem htargetMem
  have hbone : placement.tile ≠ .stone := by
    simp only [placement, reverseBonePlacement_tile]
    exact boneClass.tile_ne_stone
  have htwo := every_literal_bone_has_two_owners hstone tiling placement
    hplacement
  let edge := reverseBoneEdgeOfTiling hstone tiling source target boneClass
    hstep hsourceMem htargetMem hplacement
  have hedgeClass : IsPlacementClass placement edge.boneClass := by
    simpa [edge, placement] using edge.class_spec
  have hboneClass : IsPlacementClass placement boneClass := by
    simpa [placement] using reverseBonePlacement_isClass source target
      boneClass hstep hsourceMem htargetMem
  have hedgeUnique := (exists_unique_goodBoneClass placement hbone htwo).choose_spec.2
    edge.boneClass hedgeClass
  have hclassUnique := (exists_unique_goodBoneClass placement hbone htwo).choose_spec.2
    boneClass hboneClass
  exact hedgeUnique.trans hclassUnique.symm

theorem reverseBoneEdgeOfTiling_source
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1) :
    (reverseBoneEdgeOfTiling hstone tiling source target boneClass hstep
      hsourceMem htargetMem hplacement).source = source := by
  let edge := reverseBoneEdgeOfTiling hstone tiling source target boneClass
    hstep hsourceMem htargetMem hplacement
  have hclass := reverseBoneEdgeOfTiling_class hstone tiling source target
    boneClass hstep hsourceMem htargetMem hplacement
  apply owner_coordinates_injective
  · rw [edge.source_anchor.1, reverseBoneEdgeOfTiling_placement,
      reverseBonePlacement_base, hclass]
    have h := reverseBoneBase_source_anchor source boneClass
    exact congrArg Prod.fst h
  · rw [edge.source_anchor.2, reverseBoneEdgeOfTiling_placement,
      reverseBonePlacement_base, hclass]
    have h := reverseBoneBase_source_anchor source boneClass
    exact congrArg Prod.snd h

theorem reverseBoneEdgeOfTiling_target
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1) :
    (reverseBoneEdgeOfTiling hstone tiling source target boneClass hstep
      hsourceMem htargetMem hplacement).target = target := by
  let edge := reverseBoneEdgeOfTiling hstone tiling source target boneClass
    hstep hsourceMem htargetMem hplacement
  have hclass := reverseBoneEdgeOfTiling_class hstone tiling source target
    boneClass hstep hsourceMem htargetMem hplacement
  apply owner_coordinates_injective
  · rw [edge.target_anchor.1, reverseBoneEdgeOfTiling_placement,
      reverseBonePlacement_base, hclass]
    have h := reverseBoneBase_target_anchor source target boneClass hstep
    exact congrArg Prod.fst h
  · rw [edge.target_anchor.2, reverseBoneEdgeOfTiling_placement,
      reverseBonePlacement_base, hclass]
    have h := reverseBoneBase_target_anchor source target boneClass hstep
    exact congrArg Prod.snd h

theorem literalDirectedEdge_placement_eq_reverse {m : ℕ}
    (edge : LiteralDirectedEdge m) :
    edge.placement = reverseBonePlacement edge.source edge.target
      edge.boneClass (literalDirectedEdge_anchor_step edge)
      (literalDirectedEdge_source_cell_mem edge)
      (literalDirectedEdge_target_cell_mem edge) := by
  apply Subtype.ext
  apply Prod.ext
  · exact edge.class_spec.1
  · apply Subtype.ext
    change edge.placement.base = reverseBoneBase edge.source edge.boneClass
    apply Prod.ext
    · have hq := edge.source_anchor.1
      simp [reverseBoneBase]
      omega
    · have hr := edge.source_anchor.2
      simp [reverseBoneBase]
      omega

theorem reverseBonePlacement_eq_edge_of_source_class {m : ℕ}
    (edge : LiteralDirectedEdge m)
    (source target : SimplexPoint (m + 3))
    (boneClass : GoodBoneClass)
    (hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label))
    (hsource : source = edge.source)
    (hclass : boneClass = edge.boneClass) :
    reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem = edge.placement := by
  rw [literalDirectedEdge_placement_eq_reverse edge]
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg GoodBoneClass.tile hclass
  · apply Subtype.ext
    change reverseBoneBase source boneClass =
      reverseBoneBase edge.source edge.boneClass
    rw [hsource, hclass]

end BenzelProblem6Kernel
