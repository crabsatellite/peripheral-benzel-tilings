import D4KernelOnly.GeneralClassMinusOneTerminalSupportGraph

/-! # Closed contours in the class-minus-one terminal tree are trivial -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem cmoTerminalWalkDeleteEdge_nonempty
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    (removed : LabeledHexEdge)
    (hremoved : removed ∈ (cmoReducedRightmostTerminal hs tiling).edges)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (cmoReducedRightmostTerminal hs tiling).edges)
    (hforward : removed ∉ edges)
    (hreverse : reverseLabeledHexEdge removed ∉ edges)
    (hstart : start ∈ cmoTilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ cmoTilingBoundaryVertexFinset tiling) :
    Nonempty (((cmoTerminalSupportGraph hs tiling).deleteEdges
      {s(⟨removed.source, by
          rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨removed, hremoved, rfl⟩⟩,
        ⟨removed.target, by
          rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
          have hr := cmoReducedRightmostTerminal_reverse_mem hs tiling hremoved
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨reverseLabeledHexEdge removed, hr, rfl⟩⟩)}).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  let removedSource : ↥(cmoTilingBoundaryVertexFinset tiling) :=
    ⟨removed.source, by
      rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨removed, hremoved, rfl⟩⟩
  let removedTarget : ↥(cmoTilingBoundaryVertexFinset tiling) :=
    ⟨removed.target, by
      rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
      have hr := cmoReducedRightmostTerminal_reverse_mem hs tiling hremoved
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨reverseLabeledHexEdge removed, hr, rfl⟩⟩
  let H := (cmoTerminalSupportGraph hs tiling).deleteEdges
    {s(removedSource, removedTarget)}
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
      have hedge : edge ∈ (cmoReducedRightmostTerminal hs tiling).edges :=
        hsubset (by simp)
      have htarget : edge.target ∈ cmoTilingBoundaryVertexFinset tiling := by
        rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
        have hr := cmoReducedRightmostTerminal_reverse_mem hs tiling hedge
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge, hr, rfl⟩
      have hedgeNe :
          s((⟨edge.source, hstart⟩ : ↥(cmoTilingBoundaryVertexFinset tiling)),
            (⟨edge.target, htarget⟩ : ↥(cmoTilingBoundaryVertexFinset tiling))) ≠
          s(removedSource, removedTarget) := by
        intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with heq | heq
        · have hphysical : edge = removed :=
            cmoTerminal_edge_endpoint_injective hs tiling hedge hremoved
              (congrArg Subtype.val heq.1) (congrArg Subtype.val heq.2)
          exact hforward (by simp [hphysical])
        · have hr := cmoReducedRightmostTerminal_reverse_mem hs tiling hremoved
          have hphysical : edge = reverseLabeledHexEdge removed :=
            cmoTerminal_edge_endpoint_injective hs tiling hedge hr
              (congrArg Subtype.val heq.1) (congrArg Subtype.val heq.2)
          exact hreverse (by simp [hphysical])
      have hadjH : H.Adj
          ⟨edge.source, hstart⟩ ⟨edge.target, htarget⟩ := by
        simp [H, SimpleGraph.deleteEdges, hedgeNe]
        exact ⟨edge, hedge, rfl, rfl⟩
      have htail := ih
        (fun item hitem => hsubset (by simp [hitem]))
        (by intro hmem; exact hforward (by simp [hmem]))
        (by intro hmem; exact hreverse (by simp [hmem]))
        htarget hfinish
      obtain ⟨tailWalk⟩ := htail
      exact ⟨SimpleGraph.Walk.cons hadjH tailWalk⟩

theorem cmoTerminalTree_closed_word_empty
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    (root : HexVertex) (edges : List LabeledHexEdge)
    (path : ContinuousLabeledEdgePath root edges root)
    (hsubset : edges ⊆ (cmoReducedRightmostTerminal hs tiling).edges)
    (hnodup : edges.Nodup) :
    InvolutiveWordEquivalent (labeledEdgeWord edges) [] := by
  generalize hlen : edges.length = n
  induction n using Nat.strong_induction_on generalizing root edges
  all_goals rename_i n ih
  cases edges with
  | nil => exact Relation.EqvGen.refl _
  | cons edge rest =>
      cases path with
      | cons _ tail =>
          have hedge : edge ∈ (cmoReducedRightmostTerminal hs tiling).edges :=
            hsubset (by simp)
          have hrestSubset : rest ⊆
              (cmoReducedRightmostTerminal hs tiling).edges := by
            intro item hitem
            exact hsubset (by simp [hitem])
          have hforward : edge ∉ rest := (List.nodup_cons.mp hnodup).1
          have hsourceVertex : edge.source ∈
              cmoTilingBoundaryVertexFinset tiling := by
            rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
            simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
            exact ⟨edge, hedge, rfl⟩
          have htargetVertex : edge.target ∈
              cmoTilingBoundaryVertexFinset tiling := by
            rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
            have hr := cmoReducedRightmostTerminal_reverse_mem hs tiling hedge
            simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
            exact ⟨reverseLabeledHexEdge edge, hr, rfl⟩
          have hreverseMem : reverseLabeledHexEdge edge ∈ rest := by
            by_contra hreverse
            obtain ⟨deletedWalk⟩ := cmoTerminalWalkDeleteEdge_nonempty
              hs tiling edge hedge tail hrestSubset hforward hreverse
                htargetVertex hsourceVertex
            have hbridge :=
              (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
                (cmoTerminalSupportGraph_isTree hs tiling).IsAcyclic)
                (show (cmoTerminalSupportGraph hs tiling).Adj
                  ⟨edge.source, hsourceVertex⟩
                  ⟨edge.target, htargetVertex⟩ from
                    ⟨edge, hedge, rfl, rfl⟩)
            apply ((SimpleGraph.isBridge_iff).mp hbridge).2
            simpa [SimpleGraph.deleteEdges] using deletedWalk.reachable.symm
          obtain ⟨middle, suffix, hsplit⟩ :=
            List.mem_iff_append.mp hreverseMem
          have hprefixPath := tail
          rw [hsplit] at hprefixPath
          have prefixClosed := hprefixPath.prefix_before_edge
            (segment := middle) (suffix := suffix)
            (edge := reverseLabeledHexEdge edge)
          have suffixClosed := hprefixPath.suffix_after_edge
            (segment := middle) (suffix := suffix)
            (edge := reverseLabeledHexEdge edge)
          have hprefixSubset : middle ⊆
              (cmoReducedRightmostTerminal hs tiling).edges := by
            intro item hitem
            exact hrestSubset (by rw [hsplit]; simp [hitem])
          have hsuffixSubset : suffix ⊆
              (cmoReducedRightmostTerminal hs tiling).edges := by
            intro item hitem
            exact hrestSubset (by rw [hsplit]; simp [hitem])
          have hrestNodup := (List.nodup_cons.mp hnodup).2
          rw [hsplit, List.nodup_append, List.nodup_cons] at hrestNodup
          have hprefixNodup := hrestNodup.1
          have hsuffixNodup := hrestNodup.2.1.2
          have hmiddleLength : middle.length < (edge :: rest).length := by
            rw [hsplit]
            simp
            omega
          have hsuffixLength : suffix.length < (edge :: rest).length := by
            rw [hsplit]
            simp
            omega
          have hprefix := ih middle.length (by omega)
            edge.target middle prefixClosed hprefixSubset hprefixNodup rfl
          have hsuffix := ih suffix.length (by omega)
            edge.source suffix suffixClosed hsuffixSubset hsuffixNodup rfl
          have hreplacePrefix := involutiveWordEquivalent_append_context
            [edge.label] (edge.label :: labeledEdgeWord suffix) hprefix
          have hpair : InvolutiveWordEquivalent [edge.label, edge.label] [] :=
            Relation.EqvGen.rel _ _
              (InvolutionCancelStep.cancel [] [] edge.label)
          have hcancelPair := involutiveWordEquivalent_append_right
            hpair (labeledEdgeWord suffix)
          have hshape : labeledEdgeWord
              (edge :: (middle ++ reverseLabeledHexEdge edge :: suffix)) =
              [edge.label] ++ labeledEdgeWord middle ++
                edge.label :: labeledEdgeWord suffix := by
            simp [labeledEdgeWord, List.map_append, List.append_assoc]
          rw [hsplit, hshape]
          exact Relation.EqvGen.trans _ _ _ hreplacePrefix
            (Relation.EqvGen.trans _ _ _ (by simpa using hcancelPair) hsuffix)

theorem cmoReducedRightmostTerminal_word_empty
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    InvolutiveWordEquivalent
      (labeledEdgeWord (cmoReducedRightmostTerminal hs tiling).edges) [] := by
  exact cmoTerminalTree_closed_word_empty hs tiling
    (cmoReducedRightmostTerminal hs tiling).root
    (cmoReducedRightmostTerminal hs tiling).edges
    (cmoReducedRightmostTerminal hs tiling).continuous
    (fun _ h => h) (cmoReducedRightmostTerminal_nodup hs tiling)

end FiniteDefects
