import D4KernelOnly.GeneralClassZeroDownVertexSurjection

/-! # Cardinality of the class-zero down-type vertex carrier -/

namespace FiniteDefects

abbrev CZDownPhase0Missing (s r : ℕ) :=
  {p : CMOTruncatedPoint (2 * s + r - 1) s //
    p.1.w = 2 * s + r - 1 - s + 1 ∨
      p.1.v = 2 * s + r - 1 - s + 1}

noncomputable instance czDownPhase0ParameterFintype (s r : ℕ) :
    Fintype (CZDownPhase0Parameter s r) := Fintype.ofFinite _
noncomputable instance czDownPhase1ParameterFintype (s r : ℕ) :
    Fintype (CZDownPhase1Parameter s r) := Fintype.ofFinite _
noncomputable instance czDownPhase2ParameterFintype (s r : ℕ) :
    Fintype (CZDownPhase2Parameter s r) := Fintype.ofFinite _
noncomputable instance czDownPhase0MissingFintype (s r : ℕ) :
    Fintype (CZDownPhase0Missing s r) := Fintype.ofFinite _

def czBoundaryWInDownDomain
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : BoundaryW (2 * s + r - 1) s) :
    CMOTruncatedPoint (2 * s + r - 1) s :=
  ⟨p.1, by
    have hsum := p.1.sum_eq
    have hw := p.2
    simp only [inTruncatedOwnerDomain]
    omega⟩

def czBoundaryVInDownDomain
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : BoundaryV (2 * s + r - 1) s) :
    CMOTruncatedPoint (2 * s + r - 1) s :=
  ⟨p.1, by
    have hsum := p.1.sum_eq
    have hv := p.2
    simp only [inTruncatedOwnerDomain]
    omega⟩

def czDownPhase0MissingEquivBoundarySum
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    CZDownPhase0Missing s r ≃
      BoundaryW (2 * s + r - 1) s ⊕ BoundaryV (2 * s + r - 1) s where
  toFun p := by
    by_cases hw : p.1.1.w = 2 * s + r - 1 - s + 1
    · exact .inl ⟨p.1.1, hw⟩
    · exact .inr ⟨p.1.1, p.2.resolve_left hw⟩
  invFun boundary := by
    rcases boundary with p | p
    · exact ⟨czBoundaryWInDownDomain s r hs hr p, Or.inl p.2⟩
    · exact ⟨czBoundaryVInDownDomain s r hs hr p, Or.inr p.2⟩
  left_inv := by
    intro p; apply Subtype.ext; apply Subtype.ext
    dsimp
    by_cases hw : p.1.1.w = 2 * s + r - 1 - s + 1
    · simp [hw, czBoundaryWInDownDomain]
    · simp [hw, czBoundaryVInDownDomain]
  right_inv := by
    intro boundary
    rcases boundary with p | p
    · simp [p.2, czBoundaryWInDownDomain]
    · have hsum := p.1.sum_eq
      have hv := p.2
      have hw : p.1.w ≠ 2 * s + r - 1 - s + 1 := by
        intro heq; omega
      simp [hw, czBoundaryVInDownDomain]

theorem card_czDownPhase0Missing
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Fintype.card (CZDownPhase0Missing s r) = 2 * s := by
  rw [Fintype.card_congr (czDownPhase0MissingEquivBoundarySum s r hs hr),
    Fintype.card_sum,
    card_boundaryW (2 * s + r - 1) s (by omega),
    card_boundaryV (2 * s + r - 1) s (by omega)]
  omega

noncomputable def czDownPhase0PresentMissingEquiv (s r : ℕ) :
    CZDownPhase0Parameter s r ⊕ CZDownPhase0Missing s r ≃
      CMOTruncatedPoint (2 * s + r - 1) s where
  toFun item := by rcases item with p | p <;> exact p.1
  invFun p := by
    by_cases hw : p.1.w = 2 * s + r - 1 - s + 1
    · exact .inr ⟨p, Or.inl hw⟩
    · by_cases hv : p.1.v = 2 * s + r - 1 - s + 1
      · exact .inr ⟨p, Or.inr hv⟩
      · exact .inl ⟨p, hw, hv⟩
  left_inv := by
    intro item
    rcases item with p | p
    · dsimp; simp [p.2.1, p.2.2]
    · dsimp
      rcases p.2 with hw | hv
      · simp [hw]
      · by_cases hw : p.1.1.w = 2 * s + r - 1 - s + 1
        · simp [hw]
        · simp [hw, hv]
  right_inv := by
    intro p
    by_cases hw : p.1.w = 2 * s + r - 1 - s + 1
    · simp [hw]
    · by_cases hv : p.1.v = 2 * s + r - 1 - s + 1 <;> simp [hw, hv]

theorem card_czDownPhase0Parameter
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Fintype.card (CZDownPhase0Parameter s r) =
      Fintype.card (CMOTruncatedPoint (2 * s + r - 1) s) - 2 * s := by
  have hpartition := Fintype.card_congr (czDownPhase0PresentMissingEquiv s r)
  rw [Fintype.card_sum, card_czDownPhase0Missing s r hs hr] at hpartition
  omega

def czDownPhase1EquivPhase0 (s r : ℕ) :
    CZDownPhase1Parameter s r ≃ CZDownPhase0Parameter s r where
  toFun p :=
    ⟨⟨rotateOwner _ (rotateOwner _ p.1.1), by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.2, h.1, h.2.1⟩⟩,
      by simpa [rotateOwner] using p.2.1,
      by simpa [rotateOwner] using p.2.2⟩
  invFun p :=
    ⟨⟨rotateOwner _ p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.1, h.2.2, h.1⟩⟩,
      by simpa [rotateOwner] using p.2.1,
      by simpa [rotateOwner] using p.2.2⟩
  left_inv := by intro p; apply Subtype.ext; apply Subtype.ext; apply simplexPoint_ext <;> rfl
  right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; apply simplexPoint_ext <;> rfl

def czDownPhase2EquivPhase0 (s r : ℕ) :
    CZDownPhase2Parameter s r ≃ CZDownPhase0Parameter s r where
  toFun p :=
    ⟨⟨rotateOwner _ p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.1, h.2.2, h.1⟩⟩,
      by simpa [rotateOwner] using p.2.2,
      by simpa [rotateOwner] using p.2.1⟩
  invFun p :=
    ⟨⟨(rotateOwner _).symm p.1.1, by
        have h := p.1.2
        simp [inTruncatedOwnerDomain, rotateOwner] at h ⊢
        exact ⟨h.2.2, h.1, h.2.1⟩⟩,
      by simpa [rotateOwner] using p.2.2,
      by simpa [rotateOwner] using p.2.1⟩
  left_inv := by intro p; apply Subtype.ext; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; simp

abbrev CZDownVertexParameterSum (s r : ℕ) :=
  CZDownPhase0Parameter s r ⊕
    (CZDownPhase1Parameter s r ⊕ CZDownPhase2Parameter s r)

def czDownVertexParameterEquivSum (s r : ℕ) :
    CZDownVertexParameter s r ≃ CZDownVertexParameterSum s r where
  toFun
    | .phase0 p => .inl p
    | .phase1 p => .inr (.inl p)
    | .phase2 p => .inr (.inr p)
  invFun
    | .inl p => .phase0 p
    | .inr (.inl p) => .phase1 p
    | .inr (.inr p) => .phase2 p
  left_inv := by intro p; cases p <;> rfl
  right_inv := by intro p; rcases p with p | p; rfl; rcases p <;> rfl

noncomputable def czDownVertexParameterFintype (s r : ℕ) :
    Fintype (CZDownVertexParameter s r) :=
  Fintype.ofEquiv (CZDownVertexParameterSum s r)
    (czDownVertexParameterEquivSum s r).symm

noncomputable def czDownVertexParameterEquiv
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    CZDownVertexParameter s r ≃
      ↥(offsetDownAnchorFinset (2 * s + r - 2) (3 * s)) :=
  Equiv.ofBijective (czDownParameterToAnchor s r hs hr)
    ⟨by
      intro a b h
      exact czDownParameterAnchor_injective s r (congrArg Subtype.val h),
      czDownParameterToAnchor_surjective s r hs hr⟩

theorem card_czDownAnchor
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (offsetDownAnchorFinset (2 * s + r - 2) (3 * s)).card =
      3 * ((2 * s + r + 1).choose 2 - 3 * s.choose 2 - 2 * s) := by
  letI := czDownVertexParameterFintype s r
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (czDownVertexParameterEquiv s r hs hr),
    Fintype.card_congr (czDownVertexParameterEquivSum s r),
    Fintype.card_sum, Fintype.card_sum,
    Fintype.card_congr (czDownPhase1EquivPhase0 s r),
    Fintype.card_congr (czDownPhase2EquivPhase0 s r),
    card_czDownPhase0Parameter s r hs hr,
    card_cmoTruncatedPoint_of_room (2 * s + r - 1) s hs (by omega)]
  rw [show 2 * s + r - 1 + 2 = 2 * s + r + 1 by omega]
  omega

theorem twice_card_czDownAnchor
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    2 * (offsetDownAnchorFinset (2 * s + r - 2) (3 * s)).card =
      3 * s * s + 3 * r * r + 12 * s * r + 3 * s + 3 * r := by
  rw [card_czDownAnchor s r hs hr]
  have hS := twice_choose_two_int s hs
  have hA := twice_choose_two_int (2 * s + r + 1) (by omega)
  push_cast at hS hA
  have hle : 3 * s.choose 2 ≤ (2 * s + r + 1).choose 2 := by
    exact_mod_cast (show 3 * (s.choose 2 : ℤ) ≤
      ((2 * s + r + 1).choose 2 : ℤ) by nlinarith)
  have h2sZ : (2 * s : ℤ) ≤ ((2 * s + r + 1).choose 2 : ℤ) -
      3 * (s.choose 2 : ℤ) := by nlinarith
  have h2s : 2 * s ≤ (2 * s + r + 1).choose 2 - 3 * s.choose 2 := by
    have hz : (2 * s : ℤ) ≤
        (((2 * s + r + 1).choose 2 - 3 * s.choose 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle]; push_cast; exact h2sZ
    exact_mod_cast hz
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub h2s, Nat.cast_sub hle]
  push_cast
  nlinarith

end FiniteDefects
