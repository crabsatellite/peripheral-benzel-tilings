import BenzelProblem6Kernel.TerminalSupportGraph

/-! # Closed contours in the terminal tree are involutively trivial -/

namespace BenzelProblem6Kernel

theorem terminalWalkDeleteEdge_nonempty {m : ℕ}
    (tiling : LiteralTiling m) (removed : LabeledHexEdge)
    (hremoved : removed ∈
      (literalTilingRightmostTerminal tiling).edges)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (literalTilingRightmostTerminal tiling).edges)
    (hforward : removed ∉ edges)
    (hreverse : reverseLabeledHexEdge removed ∉ edges)
    (hstart : start ∈ tilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ tilingBoundaryVertexFinset tiling) :
    Nonempty (((terminalSupportGraph tiling).deleteEdges
      {s(⟨removed.source, by
          rw [← terminal_source_eq_boundaryVertices]
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨removed, hremoved, rfl⟩⟩,
        ⟨removed.target, by
          rw [← terminal_source_eq_boundaryVertices]
          have hr := literalTilingRightmostTerminal_reverse_mem
            tiling hremoved
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨reverseLabeledHexEdge removed, hr, rfl⟩⟩)}).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  let removedSource : ↥(tilingBoundaryVertexFinset tiling) :=
    ⟨removed.source, by
      rw [← terminal_source_eq_boundaryVertices]
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨removed, hremoved, rfl⟩⟩
  let removedTarget : ↥(tilingBoundaryVertexFinset tiling) :=
    ⟨removed.target, by
      rw [← terminal_source_eq_boundaryVertices]
      have hr := literalTilingRightmostTerminal_reverse_mem tiling hremoved
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨reverseLabeledHexEdge removed, hr, rfl⟩⟩
  let H := (terminalSupportGraph tiling).deleteEdges
    {s(removedSource, removedTarget)}
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
      have hedge : edge ∈
          (literalTilingRightmostTerminal tiling).edges :=
        hsubset (by simp)
      have htarget : edge.target ∈ tilingBoundaryVertexFinset tiling := by
        rw [← terminal_source_eq_boundaryVertices]
        have hr := literalTilingRightmostTerminal_reverse_mem tiling hedge
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge, hr, rfl⟩
      have hedgeNe :
          s((⟨edge.source, hstart⟩ :
              ↥(tilingBoundaryVertexFinset tiling)),
            (⟨edge.target, htarget⟩ :
              ↥(tilingBoundaryVertexFinset tiling))) ≠
          s(removedSource, removedTarget) := by
        intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with heq | heq
        · have hphysical : edge = removed :=
            terminal_edge_endpoint_injective tiling hedge hremoved
              (congrArg Subtype.val heq.1)
              (congrArg Subtype.val heq.2)
          exact hforward (by simp [hphysical])
        · have hr := literalTilingRightmostTerminal_reverse_mem
            tiling hremoved
          have hphysical : edge = reverseLabeledHexEdge removed :=
            terminal_edge_endpoint_injective tiling hedge hr
              (congrArg Subtype.val heq.1)
              (congrArg Subtype.val heq.2)
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

theorem terminalTree_closed_word_empty {m : ℕ}
    (tiling : LiteralTiling m)
    (root : HexVertex) (edges : List LabeledHexEdge)
    (path : ContinuousLabeledEdgePath root edges root)
    (hsubset : edges ⊆ (literalTilingRightmostTerminal tiling).edges)
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
          have hedge : edge ∈
              (literalTilingRightmostTerminal tiling).edges :=
            hsubset (by simp)
          have hrestSubset : rest ⊆
              (literalTilingRightmostTerminal tiling).edges := by
            intro item hitem
            exact hsubset (by simp [hitem])
          have hforward : edge ∉ rest := (List.nodup_cons.mp hnodup).1
          have hsourceVertex : edge.source ∈
              tilingBoundaryVertexFinset tiling := by
            rw [← terminal_source_eq_boundaryVertices]
            simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
            exact ⟨edge, hedge, rfl⟩
          have htargetVertex : edge.target ∈
              tilingBoundaryVertexFinset tiling := by
            rw [← terminal_source_eq_boundaryVertices]
            have hr := literalTilingRightmostTerminal_reverse_mem tiling hedge
            simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
            exact ⟨reverseLabeledHexEdge edge, hr, rfl⟩
          have hreverseMem : reverseLabeledHexEdge edge ∈ rest := by
            by_contra hreverse
            obtain ⟨deletedWalk⟩ := terminalWalkDeleteEdge_nonempty
              tiling edge hedge tail hrestSubset hforward hreverse
                htargetVertex hsourceVertex
            have hbridge :=
              (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
                (terminalSupportGraph_isTree tiling).IsAcyclic)
                (show (terminalSupportGraph tiling).Adj
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
              (literalTilingRightmostTerminal tiling).edges := by
            intro item hitem
            exact hrestSubset (by rw [hsplit]; simp [hitem])
          have hsuffixSubset : suffix ⊆
              (literalTilingRightmostTerminal tiling).edges := by
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
            simp [labeledEdgeWord, List.map_append,
              List.append_assoc]
          rw [hsplit, hshape]
          exact Relation.EqvGen.trans _ _ _ hreplacePrefix
            (Relation.EqvGen.trans _ _ _ (by simpa using hcancelPair) hsuffix)
theorem literalTilingRightmostTerminal_word_empty {m : ℕ}
    (tiling : LiteralTiling m) :
    InvolutiveWordEquivalent
      (labeledEdgeWord (literalTilingRightmostTerminal tiling).edges) [] := by
  exact terminalTree_closed_word_empty tiling
    (literalTilingRightmostTerminal tiling).root
    (literalTilingRightmostTerminal tiling).edges
    (literalTilingRightmostTerminal tiling).continuous
    (fun _ h => h) (literalTilingRightmostTerminal_nodup tiling)

end BenzelProblem6Kernel
