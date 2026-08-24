import BenzelProblem6Kernel.DownBenzelVertexSurjection

/-! # The finite geometric vertex carrier of the peripheral benzel -/

namespace BenzelProblem6Kernel

def upHexVertex (anchor : Cell) : HexVertex :=
  (anchor.1 + 2 * anchor.2, -anchor.1 + anchor.2)

def downHexVertex (anchor : Cell) : HexVertex :=
  (anchor.1 + 2 * anchor.2, -anchor.1 + anchor.2 + 1)

theorem upHexVertex_injective : Function.Injective upHexVertex := by
  rintro ⟨q, r⟩ ⟨q', r'⟩ h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [upHexVertex] at hx hy
    omega
  · have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [upHexVertex] at hx hy
    omega

theorem downHexVertex_injective : Function.Injective downHexVertex := by
  rintro ⟨q, r⟩ ⟨q', r'⟩ h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [downHexVertex] at hx hy
    omega
  · have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [downHexVertex] at hx hy
    omega

theorem upHexVertex_ne_downHexVertex
    (up down : Cell) : upHexVertex up ≠ downHexVertex down := by
  rintro h
  rcases up with ⟨q, r⟩
  rcases down with ⟨q', r'⟩
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [upHexVertex, downHexVertex] at hx hy
  omega

def BenzelHexVertex (m : ℕ) :=
  {vertex : HexVertex //
    (∃ anchor : UpBenzelVertexAnchor m,
      upHexVertex anchor.1 = vertex) ∨
    (∃ anchor : DownBenzelVertexAnchor m,
      downHexVertex anchor.1 = vertex)}

def benzelAnchorSumToVertex (m : ℕ) :
    UpBenzelVertexAnchor m ⊕ DownBenzelVertexAnchor m →
      BenzelHexVertex m
  | .inl anchor => ⟨upHexVertex anchor.1, Or.inl ⟨anchor, rfl⟩⟩
  | .inr anchor => ⟨downHexVertex anchor.1, Or.inr ⟨anchor, rfl⟩⟩

theorem benzelAnchorSumToVertex_injective (m : ℕ) :
    Function.Injective (benzelAnchorSumToVertex m) := by
  intro left right h
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          apply congrArg Sum.inl
          apply Subtype.ext
          apply upHexVertex_injective
          exact congrArg (fun item : BenzelHexVertex m => item.1) h
      | inr right =>
          exfalso
          exact upHexVertex_ne_downHexVertex left.1 right.1
            (congrArg (fun item : BenzelHexVertex m => item.1) h)
  | inr left =>
      cases right with
      | inl right =>
          exfalso
          exact upHexVertex_ne_downHexVertex right.1 left.1
            (congrArg (fun item : BenzelHexVertex m => item.1) h).symm
      | inr right =>
          apply congrArg Sum.inr
          apply Subtype.ext
          apply downHexVertex_injective
          exact congrArg (fun item : BenzelHexVertex m => item.1) h

theorem benzelAnchorSumToVertex_surjective (m : ℕ) :
    Function.Surjective (benzelAnchorSumToVertex m) := by
  rintro ⟨vertex, hvertex⟩
  rcases hvertex with ⟨anchor, rfl⟩ | ⟨anchor, rfl⟩
  · exact ⟨Sum.inl anchor, rfl⟩
  · exact ⟨Sum.inr anchor, rfl⟩

noncomputable def benzelAnchorSumEquivVertex (m : ℕ) :
    UpBenzelVertexAnchor m ⊕ DownBenzelVertexAnchor m ≃
      BenzelHexVertex m :=
  Equiv.ofBijective (benzelAnchorSumToVertex m)
    ⟨benzelAnchorSumToVertex_injective m,
      benzelAnchorSumToVertex_surjective m⟩

noncomputable instance benzelHexVertexFintype (m : ℕ) :
    Fintype (BenzelHexVertex m) :=
  Fintype.ofEquiv
    (UpBenzelVertexAnchor m ⊕ DownBenzelVertexAnchor m)
    (benzelAnchorSumEquivVertex m)

theorem card_benzelHexVertex_choose (m : ℕ) :
    Fintype.card (BenzelHexVertex m) =
      (m + 5).choose 2 + ((m + 6).choose 2 - 3) +
        ((m + 7).choose 2 - 6) +
          3 * ((m + 6).choose 2 - 2) := by
  rw [← Fintype.card_congr (benzelAnchorSumEquivVertex m),
    Fintype.card_sum, card_upBenzelVertexAnchor,
    card_downBenzelVertexAnchor]

theorem twice_card_benzelHexVertex (m : ℕ) :
    2 * Fintype.card (BenzelHexVertex m) =
      6 * m * m + 66 * m + 152 := by
  rw [card_benzelHexVertex_choose]
  have h5 := Nat.choose_succ_right_eq (m + 5) 1
  have h6 := Nat.choose_succ_right_eq (m + 6) 1
  have h7 := Nat.choose_succ_right_eq (m + 7) 1
  norm_num at h5 h6 h7
  have h6ge : 6 ≤ (m + 6).choose 2 := by
    nlinarith
  have h7ge : 6 ≤ (m + 7).choose 2 := by
    nlinarith
  have h6sub3 : (m + 6).choose 2 - 3 + 3 =
      (m + 6).choose 2 := Nat.sub_add_cancel (by omega)
  have h6sub2 : (m + 6).choose 2 - 2 + 2 =
      (m + 6).choose 2 := Nat.sub_add_cancel (by omega)
  have h7sub6 : (m + 7).choose 2 - 6 + 6 =
      (m + 7).choose 2 := Nat.sub_add_cancel h7ge
  nlinarith

end BenzelProblem6Kernel
