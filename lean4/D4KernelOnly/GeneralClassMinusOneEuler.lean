import D4KernelOnly.GeneralClassMinusOneArea
import D4KernelOnly.GeneralClassMinusOneTerminalAccounting

/-! # Premise-free Euler accounting for class-minus-one benzels -/

namespace FiniteDefects

theorem twice_card_cmoOffsetCellVertexFinset
    (s r : ℕ) (hs : 1 ≤ s) :
    2 * (offsetCellVertexFinset (2 * s + r - 1) (3 * s + 1)).card =
      6 * s * s + 6 * r * r + 24 * s * r + 18 * s + 18 * r + 2 := by
  rw [card_offsetCellVertexFinset]
  have hup := twice_card_cmoUpAnchorFinset s r hs
  have hdown := twice_card_cmoDownAnchorFinset s r hs
  ring_nf at hup hdown ⊢
  omega

theorem cmoTilePerimeterVertexKernelOnly : CMOTilePerimeterVertexStatement := by
  intro s r hs tiling
  have htiles := twice_cmo_tiling_card hs tiling
  have hvertices := twice_card_cmoOffsetCellVertexFinset s r hs
  rw [cmoShadowPlacementFinset_card]
  ring_nf at htiles hvertices ⊢
  omega

theorem cmoTerminal_length_add_two_eq_twice_boundary_vertices_kernelOnly
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoReducedRightmostTerminal hs tiling).edges.length + 2 =
      2 * (cmoTilingBoundaryVertexFinset tiling).card :=
  cmoTerminal_length_add_two_eq_twice_boundary_vertices
    cmoTilePerimeterVertexKernelOnly hs tiling

end FiniteDefects
