import BenzelProblem6Kernel.ConnectedGraphEdgeLowerBound

/-! # Connectivity and cardinality after deleting a nonbridge edge -/

namespace BenzelProblem6Kernel

open SimpleGraph

theorem deleteEdge_connected_of_endpoint_reachable
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {u v : V}
    (hG : G.Connected) (hadj : G.Adj u v)
    (halt : (G.deleteEdges {s(u, v)}).Reachable u v) :
    (G.deleteEdges {s(u, v)}).Connected := by
  let H := G.deleteEdges {s(u, v)}
  have edgeReachable {left right : V} (hedge : G.Adj left right) :
      H.Reachable left right := by
    by_cases heq : s(left, right) = s(u, v)
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact halt
      · exact halt.symm
    · exact (show H.Adj left right by
        simp [H, SimpleGraph.deleteEdges, hedge, heq]).reachable
  letI : Nonempty V := hG.nonempty
  refine ⟨?_⟩
  intro left right
  obtain ⟨walk⟩ := hG left right
  induction walk with
  | nil => exact .rfl
  | cons hedge tail ih => exact (edgeReachable hedge).trans ih

end BenzelProblem6Kernel
