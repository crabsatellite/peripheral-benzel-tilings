import D4KernelOnly.GeneralClassZeroTerminalSupportGraph

/-! # Closed contours in the class-zero terminal tree are trivial -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czTerminalWalkDeleteEdge_nonempty
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) (removed : LabeledHexEdge)
    (hremoved : removed ∈ (czReducedRightmostTerminal hs hr tiling).edges)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (czReducedRightmostTerminal hs hr tiling).edges)
    (hforward : removed ∉ edges)
    (hreverse : reverseLabeledHexEdge removed ∉ edges)
    (hstart : start ∈ offsetTilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ offsetTilingBoundaryVertexFinset tiling) :
    Nonempty (((czTerminalSupportGraph hs hr tiling).deleteEdges
      {s(⟨removed.source, by
          rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨removed, hremoved, rfl⟩⟩,
        ⟨removed.target, by
          rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
          have hrev := czReducedRightmostTerminal_reverse_mem hs hr tiling hremoved
          simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
          exact ⟨reverseLabeledHexEdge removed, hrev, rfl⟩⟩)}).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  let removedSource : ↥(offsetTilingBoundaryVertexFinset tiling) :=
    ⟨removed.source, by
      rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨removed, hremoved, rfl⟩⟩
  let removedTarget : ↥(offsetTilingBoundaryVertexFinset tiling) :=
    ⟨removed.target, by
      rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
      have hrev := czReducedRightmostTerminal_reverse_mem hs hr tiling hremoved
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨reverseLabeledHexEdge removed, hrev, rfl⟩⟩
  let H := (czTerminalSupportGraph hs hr tiling).deleteEdges
    {s(removedSource, removedTarget)}
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
    have hedge : edge ∈ (czReducedRightmostTerminal hs hr tiling).edges :=
      hsubset (by simp)
    have htarget : edge.target ∈ offsetTilingBoundaryVertexFinset tiling := by
      rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
      have hrev := czReducedRightmostTerminal_reverse_mem hs hr tiling hedge
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨reverseLabeledHexEdge edge, hrev, rfl⟩
    have hedgeNe :
        s((⟨edge.source, hstart⟩ : ↥(offsetTilingBoundaryVertexFinset tiling)),
          (⟨edge.target, htarget⟩ : ↥(offsetTilingBoundaryVertexFinset tiling))) ≠
        s(removedSource, removedTarget) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with heq | heq
      · have hp : edge = removed :=
          czTerminal_edge_endpoint_injective hs hr tiling hedge hremoved
            (congrArg Subtype.val heq.1) (congrArg Subtype.val heq.2)
        exact hforward (by simp [hp])
      · have hrev := czReducedRightmostTerminal_reverse_mem hs hr tiling hremoved
        have hp : edge = reverseLabeledHexEdge removed :=
          czTerminal_edge_endpoint_injective hs hr tiling hedge hrev
            (congrArg Subtype.val heq.1) (congrArg Subtype.val heq.2)
        exact hreverse (by simp [hp])
    have hadjH : H.Adj ⟨edge.source, hstart⟩ ⟨edge.target, htarget⟩ := by
      simp [H, SimpleGraph.deleteEdges, hedgeNe]
      exact ⟨edge, hedge, rfl, rfl⟩
    obtain ⟨tailWalk⟩ := ih
      (fun item hitem => hsubset (by simp [hitem]))
      (by intro hm; exact hforward (by simp [hm]))
      (by intro hm; exact hreverse (by simp [hm])) htarget hfinish
    exact ⟨SimpleGraph.Walk.cons hadjH tailWalk⟩

theorem czTerminalTree_closed_word_empty
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r)
    (root : HexVertex) (edges : List LabeledHexEdge)
    (path : ContinuousLabeledEdgePath root edges root)
    (hsubset : edges ⊆ (czReducedRightmostTerminal hs hr tiling).edges)
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
      have hedge : edge ∈ (czReducedRightmostTerminal hs hr tiling).edges :=
        hsubset (by simp)
      have hrestSubset : rest ⊆ (czReducedRightmostTerminal hs hr tiling).edges := by
        intro item hitem; exact hsubset (by simp [hitem])
      have hforward : edge ∉ rest := (List.nodup_cons.mp hnodup).1
      have hsourceVertex : edge.source ∈ offsetTilingBoundaryVertexFinset tiling := by
        rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨edge, hedge, rfl⟩
      have htargetVertex : edge.target ∈ offsetTilingBoundaryVertexFinset tiling := by
        rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
        have hrev := czReducedRightmostTerminal_reverse_mem hs hr tiling hedge
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge, hrev, rfl⟩
      have hreverseMem : reverseLabeledHexEdge edge ∈ rest := by
        by_contra hreverse
        obtain ⟨deletedWalk⟩ := czTerminalWalkDeleteEdge_nonempty
          hs hr tiling edge hedge tail hrestSubset hforward hreverse
            htargetVertex hsourceVertex
        have hbridge :=
          (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
            (czTerminalSupportGraph_isTree hs hr tiling).IsAcyclic)
            (show (czTerminalSupportGraph hs hr tiling).Adj
              ⟨edge.source, hsourceVertex⟩ ⟨edge.target, htargetVertex⟩ from
                ⟨edge, hedge, rfl, rfl⟩)
        apply ((SimpleGraph.isBridge_iff).mp hbridge).2
        simpa [SimpleGraph.deleteEdges] using deletedWalk.reachable.symm
      obtain ⟨middle, suffix, hsplit⟩ := List.mem_iff_append.mp hreverseMem
      have hprefixPath := tail
      rw [hsplit] at hprefixPath
      have prefixClosed := hprefixPath.prefix_before_edge
        (segment := middle) (suffix := suffix)
        (edge := reverseLabeledHexEdge edge)
      have suffixClosed := hprefixPath.suffix_after_edge
        (segment := middle) (suffix := suffix)
        (edge := reverseLabeledHexEdge edge)
      have hprefixSubset : middle ⊆
          (czReducedRightmostTerminal hs hr tiling).edges := by
        intro item hitem; exact hrestSubset (by rw [hsplit]; simp [hitem])
      have hsuffixSubset : suffix ⊆
          (czReducedRightmostTerminal hs hr tiling).edges := by
        intro item hitem; exact hrestSubset (by rw [hsplit]; simp [hitem])
      have hrestNodup := (List.nodup_cons.mp hnodup).2
      rw [hsplit, List.nodup_append, List.nodup_cons] at hrestNodup
      have hprefixNodup := hrestNodup.1
      have hsuffixNodup := hrestNodup.2.1.2
      have hmiddleLength : middle.length < (edge :: rest).length := by
        rw [hsplit]; simp; omega
      have hsuffixLength : suffix.length < (edge :: rest).length := by
        rw [hsplit]; simp; omega
      have hprefix := ih middle.length (by omega)
        edge.target middle prefixClosed hprefixSubset hprefixNodup rfl
      have hsuffix := ih suffix.length (by omega)
        edge.source suffix suffixClosed hsuffixSubset hsuffixNodup rfl
      have hreplacePrefix := involutiveWordEquivalent_append_context
        [edge.label] (edge.label :: labeledEdgeWord suffix) hprefix
      have hpair : InvolutiveWordEquivalent [edge.label, edge.label] [] :=
        Relation.EqvGen.rel _ _ (InvolutionCancelStep.cancel [] [] edge.label)
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

theorem czReducedRightmostTerminal_word_empty
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    InvolutiveWordEquivalent
      (labeledEdgeWord (czReducedRightmostTerminal hs hr tiling).edges) [] :=
  czTerminalTree_closed_word_empty hs hr tiling
    (czReducedRightmostTerminal hs hr tiling).root
    (czReducedRightmostTerminal hs hr tiling).edges
    (czReducedRightmostTerminal hs hr tiling).continuous
    (fun _ h => h) (czReducedRightmostTerminal_nodup hs hr tiling)

end FiniteDefects
