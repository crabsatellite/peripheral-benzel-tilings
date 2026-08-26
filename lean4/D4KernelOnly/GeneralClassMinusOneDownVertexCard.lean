import D4KernelOnly.GeneralClassMinusOneDownVertexSurjection

/-! # Cardinality of the class-minus-one down-type vertex carrier -/

namespace FiniteDefects

theorem cmoDownException0_mem_truncated
    (s r : ℕ) (hs : 1 ≤ s) :
    inTruncatedOwnerDomain (s + 1) (cmoDownException0 s r) := by
  simp [inTruncatedOwnerDomain, cmoDownException0]
  omega

theorem cmoDownException1_mem_truncated
    (s r : ℕ) (hs : 1 ≤ s) :
    inTruncatedOwnerDomain (s + 1) (cmoDownException1 s r) := by
  simp [inTruncatedOwnerDomain, cmoDownException1]
  omega

theorem cmoDownException2_mem_truncated
    (s r : ℕ) (hs : 1 ≤ s) :
    inTruncatedOwnerDomain (s + 1) (cmoDownException2 s r) := by
  simp [inTruncatedOwnerDomain, cmoDownException2]
  omega

theorem card_subtype_ne_one
    {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card {x : α // x ≠ a} = Fintype.card α - 1 := by
  have h := Fintype.card_subtype_compl (fun x : α => x = a)
  have hone : Fintype.card {x : α // x = a} = 1 := by
    apply Fintype.card_unique
  rw [hone] at h
  exact h

theorem card_fiber_ne_one
    {α β : Type} [Fintype α] [DecidableEq β]
    (f : α → β) (b : β) (a : α) (ha : f a = b)
    (hunique : ∀ x : α, f x = b → x = a) :
    Fintype.card {x : α // f x ≠ b} = Fintype.card α - 1 := by
  classical
  have h := Fintype.card_subtype_compl
    (fun x : α => f x = b)
  have hone : Fintype.card {x : α // f x = b} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨a, ha⟩, ?_⟩
    intro y
    apply Subtype.ext
    exact hunique y.1 y.2
  rw [hone] at h
  exact h

def cmoDownPhase0ParameterEquivExcluded
    (s r : ℕ) :
    CMODownPhase0Parameter s r ≃
      {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
        p.1 ≠ cmoDownException0 s r} where
  toFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def cmoDownPhase1ParameterEquivExcluded
    (s r : ℕ) :
    CMODownPhase1Parameter s r ≃
      {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
        p.1 ≠ cmoDownException1 s r} where
  toFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def cmoDownPhase2ParameterEquivExcluded
    (s r : ℕ) :
    CMODownPhase2Parameter s r ≃
      {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
        p.1 ≠ cmoDownException2 s r} where
  toFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

noncomputable instance cmoDownPhase0ParameterFintype (s r : ℕ) :
    Fintype (CMODownPhase0Parameter s r) :=
  Fintype.ofEquiv
    {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
      p.1 ≠ cmoDownException0 s r}
    (cmoDownPhase0ParameterEquivExcluded s r).symm

noncomputable instance cmoDownPhase1ParameterFintype (s r : ℕ) :
    Fintype (CMODownPhase1Parameter s r) :=
  Fintype.ofEquiv
    {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
      p.1 ≠ cmoDownException1 s r}
    (cmoDownPhase1ParameterEquivExcluded s r).symm

noncomputable instance cmoDownPhase2ParameterFintype (s r : ℕ) :
    Fintype (CMODownPhase2Parameter s r) :=
  Fintype.ofEquiv
    {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
      p.1 ≠ cmoDownException2 s r}
    (cmoDownPhase2ParameterEquivExcluded s r).symm

theorem card_cmoDownPhase0Parameter
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMODownPhase0Parameter s r) =
      Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) - 1 := by
  rw [Fintype.card_congr (cmoDownPhase0ParameterEquivExcluded s r)]
  exact card_fiber_ne_one Subtype.val (cmoDownException0 s r)
    ⟨cmoDownException0 s r, cmoDownException0_mem_truncated s r hs⟩ rfl
    (fun p h => Subtype.ext h)

theorem card_cmoDownPhase1Parameter
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMODownPhase1Parameter s r) =
      Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) - 1 := by
  rw [Fintype.card_congr (cmoDownPhase1ParameterEquivExcluded s r)]
  exact card_fiber_ne_one Subtype.val (cmoDownException1 s r)
    ⟨cmoDownException1 s r, cmoDownException1_mem_truncated s r hs⟩ rfl
    (fun p h => Subtype.ext h)

theorem card_cmoDownPhase2Parameter
    (s r : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMODownPhase2Parameter s r) =
      Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) - 1 := by
  rw [Fintype.card_congr (cmoDownPhase2ParameterEquivExcluded s r)]
  exact card_fiber_ne_one Subtype.val (cmoDownException2 s r)
    ⟨cmoDownException2 s r, cmoDownException2_mem_truncated s r hs⟩ rfl
    (fun p h => Subtype.ext h)

abbrev CMODownVertexParameterSum (s r : ℕ) :=
  CMODownPhase0Parameter s r ⊕
    (CMODownPhase1Parameter s r ⊕ CMODownPhase2Parameter s r)

def cmoDownVertexParameterEquivSum (s r : ℕ) :
    CMODownVertexParameter s r ≃ CMODownVertexParameterSum s r where
  toFun
    | .phase0 p => .inl p
    | .phase1 p => .inr (.inl p)
    | .phase2 p => .inr (.inr p)
  invFun
    | .inl p => .phase0 p
    | .inr (.inl p) => .phase1 p
    | .inr (.inr p) => .phase2 p
  left_inv := by intro parameter; cases parameter <;> rfl
  right_inv := by
    intro parameter
    rcases parameter with p | p
    · rfl
    · rcases p <;> rfl

noncomputable def cmoDownVertexParameterFintype (s r : ℕ) :
    Fintype (CMODownVertexParameter s r) :=
  Fintype.ofEquiv (CMODownVertexParameterSum s r)
    (cmoDownVertexParameterEquivSum s r).symm

noncomputable def cmoDownVertexParameterEquiv
    (s r : ℕ) (hs : 1 ≤ s) :
    CMODownVertexParameter s r ≃
      ↥(offsetDownAnchorFinset (2 * s + r - 1) (3 * s + 1)) :=
  Equiv.ofBijective (cmoDownParameterToAnchor s r hs)
    ⟨by
      intro left right h
      exact cmoDownParameterAnchor_injective s r (congrArg Subtype.val h),
      cmoDownParameterToAnchor_surjective s r hs⟩

theorem card_cmoDownVertexParameter
    (s r : ℕ) (hs : 1 ≤ s) :
    letI := cmoDownVertexParameterFintype s r
    Fintype.card (CMODownVertexParameter s r) =
      3 * (Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) - 1) := by
  letI := cmoDownVertexParameterFintype s r
  rw [Fintype.card_congr (cmoDownVertexParameterEquivSum s r),
    Fintype.card_sum, Fintype.card_sum,
    card_cmoDownPhase0Parameter s r hs,
    card_cmoDownPhase1Parameter s r hs,
    card_cmoDownPhase2Parameter s r hs]
  omega

theorem card_cmoDownAnchorFinset_as_truncated
    (s r : ℕ) (hs : 1 ≤ s) :
    (offsetDownAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      3 * (Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) - 1) := by
  letI := cmoDownVertexParameterFintype s r
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (cmoDownVertexParameterEquiv s r hs),
    card_cmoDownVertexParameter s r hs]

theorem card_cmoDownAnchorFinset_r_zero
    (s : ℕ) (hs : 1 ≤ s) :
    (offsetDownAnchorFinset (2 * s + 0 - 1) (3 * s + 1)).card =
      3 * ((s + 2).choose 2 - 1) := by
  rw [card_cmoDownAnchorFinset_as_truncated s 0 hs]
  simp only [Nat.add_zero]
  rw [card_cmoCentralTruncated s hs]

theorem card_cmoDownAnchorFinset_r_positive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (offsetDownAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      3 * (((2 * s + r + 2).choose 2 -
        3 * (s + 1).choose 2) - 1) := by
  rw [card_cmoDownAnchorFinset_as_truncated s r hs,
    card_cmoTruncatedPoint_of_room (2 * s + r) (s + 1) (by omega) (by omega)]

theorem twice_card_cmoDownAnchorFinset_r_zero
    (s : ℕ) (hs : 1 ≤ s) :
    2 * (offsetDownAnchorFinset (2 * s + 0 - 1) (3 * s + 1)).card =
      3 * s * s + 9 * s := by
  rw [card_cmoDownAnchorFinset_r_zero s hs]
  have hC := twice_choose_two_int (s + 2) (by omega)
  push_cast at hC
  have hleZ : (1 : ℤ) ≤ ((s + 2).choose 2 : ℤ) := by nlinarith
  have hle : 1 ≤ (s + 2).choose 2 := by exact_mod_cast hleZ
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hle]
  push_cast
  nlinarith

theorem twice_card_cmoDownAnchorFinset_r_positive
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    2 * (offsetDownAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      3 * s * s + 3 * r * r + 12 * s * r + 9 * s + 9 * r := by
  rw [card_cmoDownAnchorFinset_r_positive s r hs hr]
  have hS1 := twice_choose_two_int (s + 1) (by omega)
  have hA := twice_choose_two_int (2 * s + r + 2) (by omega)
  push_cast at hS1 hA
  have hleZ : 3 * ((s + 1).choose 2 : ℤ) ≤
      ((2 * s + r + 2).choose 2 : ℤ) := by
    nlinarith
  have hle : 3 * (s + 1).choose 2 ≤ (2 * s + r + 2).choose 2 := by
    exact_mod_cast hleZ
  have honeZ : (1 : ℤ) ≤
      ((2 * s + r + 2).choose 2 : ℤ) - 3 * ((s + 1).choose 2 : ℤ) := by
    nlinarith
  have hone : 1 ≤ (2 * s + r + 2).choose 2 - 3 * (s + 1).choose 2 := by
    have honeZ' : (1 : ℤ) ≤
        (( (2 * s + r + 2).choose 2 - 3 * (s + 1).choose 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle]
      push_cast
      exact honeZ
    exact_mod_cast honeZ'
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hone, Nat.cast_sub hle]
  push_cast
  nlinarith

theorem twice_card_cmoDownAnchorFinset
    (s r : ℕ) (hs : 1 ≤ s) :
    2 * (offsetDownAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      3 * s * s + 3 * r * r + 12 * s * r + 9 * s + 9 * r := by
  by_cases hr0 : r = 0
  · subst r
    simpa using twice_card_cmoDownAnchorFinset_r_zero s hs
  exact twice_card_cmoDownAnchorFinset_r_positive s r hs (by omega)

end FiniteDefects
