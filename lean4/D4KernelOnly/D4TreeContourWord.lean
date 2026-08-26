import D4KernelOnly.D4TerminalSupportGraph

/-! # Closed contours in the d=4 terminal tree are involutively trivial -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem d4TerminalWalkDeleteEdge_nonempty {m : ℕ}
    (tiling : D4LiteralTiling m) (removed : LabeledHexEdge)
    (hremoved : removed ∈ (d4ReducedRightmostTerminal tiling).edges)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (d4ReducedRightmostTerminal tiling).edges)
    (hforward : removed ∉ edges)
    (hreverse : reverseLabeledHexEdge removed ∉ edges)
    (hstart : start ∈ d4TilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ d4TilingBoundaryVertexFinset tiling) :
    Nonempty (((d4TerminalSupportGraph tiling).deleteEdges
      {s(⟨removed.source, by
          rw [← d4Terminal_source_eq_boundaryVertices]
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨removed, hremoved, rfl⟩⟩,
        ⟨removed.target, by
          rw [← d4Terminal_source_eq_boundaryVertices]
          have hr := d4ReducedRightmostTerminal_reverse_mem tiling hremoved
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨reverseLabeledHexEdge removed, hr, rfl⟩⟩)}).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  let removedSource : ↥(d4TilingBoundaryVertexFinset tiling) :=
    ⟨removed.source, by
      rw [← d4Terminal_source_eq_boundaryVertices]
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨removed, hremoved, rfl⟩⟩
  let removedTarget : ↥(d4TilingBoundaryVertexFinset tiling) :=
    ⟨removed.target, by
      rw [← d4Terminal_source_eq_boundaryVertices]
      have hr := d4ReducedRightmostTerminal_reverse_mem tiling hremoved
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨reverseLabeledHexEdge removed, hr, rfl⟩⟩
  let H := (d4TerminalSupportGraph tiling).deleteEdges
    {s(removedSource, removedTarget)}
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
      have hedge : edge ∈ (d4ReducedRightmostTerminal tiling).edges :=
        hsubset (by simp)
      have htarget : edge.target ∈ d4TilingBoundaryVertexFinset tiling := by
        rw [← d4Terminal_source_eq_boundaryVertices]
        have hr := d4ReducedRightmostTerminal_reverse_mem tiling hedge
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge, hr, rfl⟩
      have hedgeNe :
          s((⟨edge.source, hstart⟩ :
              ↥(d4TilingBoundaryVertexFinset tiling)),
            (⟨edge.target, htarget⟩ :
              ↥(d4TilingBoundaryVertexFinset tiling))) ≠
          s(removedSource, removedTarget) := by
        intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with heq | heq
        · have hphysical : edge = removed :=
            d4Terminal_edge_endpoint_injective tiling hedge hremoved
              (congrArg Subtype.val heq.1) (congrArg Subtype.val heq.2)
          exact hforward (by simp [hphysical])
        · have hr := d4ReducedRightmostTerminal_reverse_mem tiling hremoved
          have hphysical : edge = reverseLabeledHexEdge removed :=
            d4Terminal_edge_endpoint_injective tiling hedge hr
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

theorem d4TerminalTree_closed_word_empty {m : ℕ}
    (tiling : D4LiteralTiling m)
    (root : HexVertex) (edges : List LabeledHexEdge)
    (path : ContinuousLabeledEdgePath root edges root)
    (hsubset : edges ⊆ (d4ReducedRightmostTerminal tiling).edges)
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
          have hedge : edge ∈ (d4ReducedRightmostTerminal tiling).edges :=
            hsubset (by simp)
          have hrestSubset : rest ⊆
              (d4ReducedRightmostTerminal tiling).edges := by
            intro item hitem
            exact hsubset (by simp [hitem])
          have hforward : edge ∉ rest := (List.nodup_cons.mp hnodup).1
          have hsourceVertex : edge.source ∈
              d4TilingBoundaryVertexFinset tiling := by
            rw [← d4Terminal_source_eq_boundaryVertices]
            simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
            exact ⟨edge, hedge, rfl⟩
          have htargetVertex : edge.target ∈
              d4TilingBoundaryVertexFinset tiling := by
            rw [← d4Terminal_source_eq_boundaryVertices]
            have hr := d4ReducedRightmostTerminal_reverse_mem tiling hedge
            simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
            exact ⟨reverseLabeledHexEdge edge, hr, rfl⟩
          have hreverseMem : reverseLabeledHexEdge edge ∈ rest := by
            by_contra hreverse
            obtain ⟨deletedWalk⟩ := d4TerminalWalkDeleteEdge_nonempty
              tiling edge hedge tail hrestSubset hforward hreverse
                htargetVertex hsourceVertex
            have hbridge :=
              (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
                (d4TerminalSupportGraph_isTree tiling).IsAcyclic)
                (show (d4TerminalSupportGraph tiling).Adj
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
              (d4ReducedRightmostTerminal tiling).edges := by
            intro item hitem
            exact hrestSubset (by rw [hsplit]; simp [hitem])
          have hsuffixSubset : suffix ⊆
              (d4ReducedRightmostTerminal tiling).edges := by
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

theorem d4ReducedRightmostTerminal_word_empty {m : ℕ}
    (tiling : D4LiteralTiling m) :
    InvolutiveWordEquivalent
      (labeledEdgeWord (d4ReducedRightmostTerminal tiling).edges) [] := by
  exact d4TerminalTree_closed_word_empty tiling
    (d4ReducedRightmostTerminal tiling).root
    (d4ReducedRightmostTerminal tiling).edges
    (d4ReducedRightmostTerminal tiling).continuous
    (fun _ h => h) (d4ReducedRightmostTerminal_nodup tiling)

end FiniteDefects
