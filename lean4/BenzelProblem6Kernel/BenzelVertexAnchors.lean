import BenzelProblem6Kernel.BenzelVertexParameterCard

/-! # Up- and down-vertex anchors for the peripheral benzel -/

namespace BenzelProblem6Kernel

def simplexAnchor {t : ℕ} (p : SimplexPoint t) : Cell :=
  ((p.w : ℤ) - p.u, (p.u : ℤ) - p.v)

def downAnchorCell (anchor : Cell) : MicroLabel → Cell
  | .zero => anchor
  | .one => (anchor.1, anchor.2 + 1)
  | .two => (anchor.1 - 1, anchor.2 + 1)

def UpBenzelVertexAnchor (m : ℕ) :=
  {anchor : Cell // ∃ label : MicroLabel,
    inPeripheralBenzel (m + 5) (cellForOwnerAnchor anchor label)}

def DownBenzelVertexAnchor (m : ℕ) :=
  {anchor : Cell // ∃ label : MicroLabel,
    inPeripheralBenzel (m + 5) (downAnchorCell anchor label)}

def upVertexParameterAnchor {t : ℕ} :
    UpVertexParameter t → Cell
  | .inl p => simplexAnchor p
  | .inr (.inl p) => simplexAnchor p.1
  | .inr (.inr p) => simplexAnchor p.1

def downZeroSimplexAnchor {t : ℕ}
    (p : SimplexPoint (t + 1)) : Cell :=
  ((p.w : ℤ) - p.u + 1,
    (p.u : ℤ) - p.v - 1)

def downOneSimplexAnchor {t : ℕ}
    (p : SimplexPoint (t + 1)) : Cell :=
  simplexAnchor p

def downTwoSimplexAnchor {t : ℕ}
    (p : SimplexPoint (t + 1)) : Cell :=
  ((p.w : ℤ) - p.u + 1,
    (p.u : ℤ) - p.v)

def downZeroParameterAnchor {t : ℕ}
    (p : DownZeroParameter t) : Cell :=
  downZeroSimplexAnchor p.1

def downOneParameterAnchor {t : ℕ}
    (p : DownOneParameter t) : Cell :=
  downOneSimplexAnchor p.1

def downTwoParameterAnchor {t : ℕ}
    (p : DownTwoParameter t) : Cell :=
  downTwoSimplexAnchor p.1

def downVertexParameterAnchor {t : ℕ} :
    DownVertexParameter t → Cell
  | .inl p => downZeroParameterAnchor p
  | .inr (.inl p) => downOneParameterAnchor p
  | .inr (.inr p) => downTwoParameterAnchor p

theorem inPeripheralBenzel_mono {n n' : ℕ}
    (hn : n ≤ n') {cell : Cell}
    (hcell : inPeripheralBenzel n cell) :
    inPeripheralBenzel n' cell := by
  dsimp [inPeripheralBenzel] at hcell ⊢
  omega

theorem exists_anchor_phase_offset (t : ℕ) (anchor : Cell) :
    ∃ s : Fin 3, IsOwnerPhase (t + s) anchor := by
  let d : ℤ := (anchor.1 - anchor.2 - (t : ℤ)) % 3
  have hd_nonneg : 0 ≤ d := Int.emod_nonneg _ (by norm_num)
  have hd_lt : d < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hd_cases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd_cases with hd | hd | hd
  · refine ⟨⟨0, by omega⟩, ?_⟩
    rw [IsOwnerPhase, Int.modEq_iff_dvd,
      Int.dvd_iff_emod_eq_zero]
    dsimp [d] at hd
    norm_num at hd ⊢
    omega
  · refine ⟨⟨1, by omega⟩, ?_⟩
    rw [IsOwnerPhase, Int.modEq_iff_dvd,
      Int.dvd_iff_emod_eq_zero]
    dsimp [d] at hd
    norm_num at hd ⊢
    omega
  · refine ⟨⟨2, by omega⟩, ?_⟩
    rw [IsOwnerPhase, Int.modEq_iff_dvd,
      Int.dvd_iff_emod_eq_zero]
    dsimp [d] at hd
    norm_num at hd ⊢
    omega

theorem simplexAnchor_eq_owner_anchor {t : ℕ}
    (p : SimplexPoint t) :
    simplexAnchor p = (ownerQ p, ownerR p) := by
  rfl

theorem simplexAnchor_injective_at_total (t : ℕ) :
    Function.Injective (fun p : SimplexPoint t => simplexAnchor p) := by
  intro left right hanchor
  have hq : ownerQ left = ownerQ right := congrArg Prod.fst hanchor
  have hr : ownerR left = ownerR right := congrArg Prod.snd hanchor
  have hu := recover_u_numerator left
  have hu' := recover_u_numerator right
  have hv := recover_v_numerator left
  have hv' := recover_v_numerator right
  have hw := recover_w_numerator left
  have hw' := recover_w_numerator right
  apply simplexPoint_ext <;> omega

end BenzelProblem6Kernel
