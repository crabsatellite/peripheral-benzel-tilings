import D4KernelOnly.D4ZeroAnchorCount

/-! # Exact cardinality of the d=4 cell-vertex carrier -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem twice_card_d4CellVertexFinset (m : ℕ) :
    2 * (d4CellVertexFinset m).card = 6 * m * m + 54 * m + 74 := by
  cases m with
  | zero =>
      rw [card_d4CellVertexFinset,
        card_d4UpAnchorFinset_zero, card_d4DownAnchorFinset_zero]
  | succ m =>
      rw [card_d4CellVertexFinset,
        card_d4UpAnchorFinset_succ,
        card_d4DownAnchorFinset_succ]
      have hwide :
          Fintype.card (UpBenzelVertexAnchor m) +
              Fintype.card (DownBenzelVertexAnchor m) =
            Fintype.card (BenzelHexVertex m) := by
        calc
          _ = Fintype.card
              (UpBenzelVertexAnchor m ⊕ DownBenzelVertexAnchor m) := by
            rw [Fintype.card_sum]
          _ = _ := Fintype.card_congr (benzelAnchorSumEquivVertex m)
      have htwice := twice_card_benzelHexVertex m
      have hup : 3 ≤ Fintype.card (UpBenzelVertexAnchor m) := by
        rw [card_upBenzelVertexAnchor]
        have hge := Nat.choose_le_choose 2 (show 3 ≤ m + 5 by omega)
        norm_num at hge
        omega
      have hdown : 6 ≤ Fintype.card (DownBenzelVertexAnchor m) := by
        rw [card_downBenzelVertexAnchor]
        have hge : 6 ≤ (m + 6).choose 2 := by
          simpa using Nat.choose_le_choose 2 (show 4 ≤ m + 6 by omega)
        have hsub : (m + 6).choose 2 - 2 + 2 =
            (m + 6).choose 2 := Nat.sub_add_cancel (by omega)
        omega
      have hupsub :
          Fintype.card (UpBenzelVertexAnchor m) - 3 + 3 =
            Fintype.card (UpBenzelVertexAnchor m) :=
        Nat.sub_add_cancel hup
      have hdownsub :
          Fintype.card (DownBenzelVertexAnchor m) - 6 + 6 =
            Fintype.card (DownBenzelVertexAnchor m) :=
        Nat.sub_add_cancel hdown
      have hpoly :
          6 * m * m + 66 * m + 152 =
            (6 * (m + 1) * (m + 1) + 54 * (m + 1) + 74) + 18 := by
        ring
      omega

end FiniteDefects
