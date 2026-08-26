import D4KernelOnly.GeneralClassZeroDownVertexCard

/-! # Premise-free Euler accounting for class-zero benzels -/

namespace FiniteDefects

theorem twice_card_czOffsetCellVertexFinset
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    2 * (offsetCellVertexFinset (2 * s + r - 2) (3 * s)).card =
      6 * s * s + 6 * r * r + 24 * s * r + 6 * s + 6 * r - 4 := by
  rw [card_offsetCellVertexFinset]
  have hup := twice_card_czUpAnchor s r hs hr
  have hdown := twice_card_czDownAnchor s r hs hr
  have htarget : 4 ≤ 6 * s * s + 6 * r * r + 24 * s * r + 6 * s + 6 * r := by
    nlinarith
  ring_nf at hup hdown ⊢
  omega

theorem czTilePerimeterVertexKernelOnly
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    12 * tiling.1.card + (12 * (s + r) - 6) + 2 =
      2 * (offsetCellVertexFinset (2 * s + r - 2) (3 * s)).card := by
  have htiles := twice_cz_tiling_card hs hr tiling
  have hvertices := twice_card_czOffsetCellVertexFinset s r hs hr
  have hsr : s + r ≤ s * s + r * r + 4 * s * r := by nlinarith
  have hvbound : 4 ≤ 6 * s * s + 6 * r * r + 24 * s * r +
      6 * s + 6 * r := by nlinarith
  have hpbound : 6 ≤ 12 * (s + r) := by omega
  have htilesZ := congrArg (fun n : ℕ => (n : ℤ)) htiles
  have hverticesZ := congrArg (fun n : ℕ => (n : ℤ)) hvertices
  push_cast at htilesZ hverticesZ
  rw [Nat.cast_sub hsr] at htilesZ
  rw [Nat.cast_sub hvbound] at hverticesZ
  push_cast at htilesZ hverticesZ
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hpbound]
  push_cast
  nlinarith [htilesZ, hverticesZ]

end FiniteDefects
