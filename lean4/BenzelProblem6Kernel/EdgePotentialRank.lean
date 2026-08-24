import BenzelProblem6Kernel.CornerAndPassThrough

/-!
# Natural-number rank for labelled directed edges
-/

namespace BenzelProblem6Kernel

def simplexLabelPotential {t : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) : ℤ :=
  ownerPotential label (ownerQ p) (ownerR p)

theorem simplexLabelPotential_bounds {t : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) :
    -(t : ℤ) ≤ simplexLabelPotential label p ∧
      simplexLabelPotential label p ≤ t := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by exact_mod_cast p.sum_eq
  rcases label <;>
    simp [simplexLabelPotential, ownerPotential, ownerQ, ownerR] <;> omega

def simplexLabelRank {t : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) : ℕ :=
  (simplexLabelPotential label p + t).toNat

theorem simplexLabelRank_cast {t : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) :
    (simplexLabelRank label p : ℤ) = simplexLabelPotential label p + t := by
  unfold simplexLabelRank
  exact Int.toNat_of_nonneg (by
    have := (simplexLabelPotential_bounds label p).1
    omega)

theorem literalDirectedEdge_potential_succ {m : ℕ}
    (edge : LiteralDirectedEdge m) :
    simplexLabelPotential edge.boneClass.label edge.target =
      simplexLabelPotential edge.boneClass.label edge.source + 1 := by
  have hinc := allowedStep_potential_increase edge.boneClass.label
    (ownerQ edge.source) (ownerR edge.source)
    edge.boneClass.step.1 edge.boneClass.step.2
    (literalDirectedEdge_allowed edge)
  have hstep := literalDirectedEdge_anchor_step edge
  have hq := congrArg Prod.fst hstep
  have hr := congrArg Prod.snd hstep
  simp only [addCell] at hq hr
  simp [simplexLabelPotential]
  rw [← hq, ← hr]
  exact hinc

theorem literalDirectedEdge_rank_succ {m : ℕ}
    (edge : LiteralDirectedEdge m) :
    simplexLabelRank edge.boneClass.label edge.target =
      simplexLabelRank edge.boneClass.label edge.source + 1 := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [simplexLabelRank_cast, simplexLabelRank_cast,
    literalDirectedEdge_potential_succ]
  ring

theorem incoming_rank_lt_source_rank {m : ℕ}
    (inEdge outEdge : LiteralDirectedEdge m)
    (hmeet : inEdge.target = outEdge.source)
    (hlabel : inEdge.boneClass.label = outEdge.boneClass.label) :
    simplexLabelRank outEdge.boneClass.label inEdge.source <
      simplexLabelRank outEdge.boneClass.label outEdge.source := by
  have hsucc := literalDirectedEdge_rank_succ inEdge
  rw [hlabel] at hsucc
  rw [hmeet] at hsucc
  omega

end BenzelProblem6Kernel
