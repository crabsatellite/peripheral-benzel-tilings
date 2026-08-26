import D4KernelOnly.GeneralClassMinusOneTilingVertices

/-! # Exact cell and vertex counts for class-minus-one benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

abbrev CMOTruncatedPoint (N k : ℕ) :=
  {p : SimplexPoint N // inTruncatedOwnerDomain k p}

noncomputable instance cmoTruncatedPointFintype (N k : ℕ) :
    Fintype (CMOTruncatedPoint N k) := Fintype.ofFinite _

theorem card_cmoTruncatedPoint_of_room
    (N k : ℕ) (hk : 1 ≤ k) (hroom : 2 * k ≤ N + 1) :
    Fintype.card (CMOTruncatedPoint N k) =
      (N + 2).choose 2 - 3 * k.choose 2 := by
  classical
  have hcomp := Fintype.card_subtype_compl
    (fun p : SimplexPoint N => ¬inTruncatedOwnerDomain k p)
  have heq : {p : SimplexPoint N // ¬¬inTruncatedOwnerDomain k p} ≃
      CMOTruncatedPoint N k :=
    Equiv.subtypeEquivProp (by funext p; apply propext; simp)
  have hcardeq := Fintype.card_congr heq
  rw [hcardeq, card_outsideTruncatedOwnerDomain N k hk hroom,
    card_simplexPoint] at hcomp
  exact hcomp

def cmoCentralTruncatedEquiv (s : ℕ) (hs : 1 ≤ s) :
    CMOTruncatedPoint (2 * s) (s + 1) ≃ SimplexPoint s where
  toFun p :=
    { u := s - p.1.u
      v := s - p.1.v
      w := s - p.1.w
      sum_eq := by
        have hsum := p.1.sum_eq
        have hb := p.2
        simp only [inTruncatedOwnerDomain] at hb
        omega }
  invFun q :=
    ⟨{ u := s - q.u
       v := s - q.v
       w := s - q.w
       sum_eq := by have hsum := q.sum_eq; omega }, by
      simp only [inTruncatedOwnerDomain]
      have hsum := q.sum_eq
      omega⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext <;>
      simp only <;>
      have hb := p.2 <;>
      simp only [inTruncatedOwnerDomain] at hb <;>
      omega
  right_inv := by
    intro q
    apply simplexPoint_ext <;>
      simp only <;>
      have hsum := q.sum_eq <;>
      omega

theorem card_cmoCentralTruncated (s : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMOTruncatedPoint (2 * s) (s + 1)) =
      (s + 2).choose 2 := by
  rw [Fintype.card_congr (cmoCentralTruncatedEquiv s hs), card_simplexPoint]

def cmoNearCentralTruncatedEquiv (s : ℕ) (hs : 1 ≤ s) :
    CMOTruncatedPoint (2 * s + 1) (s + 2) ≃ SimplexPoint (s - 1) where
  toFun p :=
    { u := s - p.1.u
      v := s - p.1.v
      w := s - p.1.w
      sum_eq := by
        have hsum := p.1.sum_eq
        have hb := p.2
        simp only [inTruncatedOwnerDomain] at hb
        omega }
  invFun q :=
    ⟨{ u := s - q.u
       v := s - q.v
       w := s - q.w
       sum_eq := by have hsum := q.sum_eq; omega }, by
      simp only [inTruncatedOwnerDomain]
      have hsum := q.sum_eq
      omega⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext <;>
      simp only <;>
      have hb := p.2 <;>
      simp only [inTruncatedOwnerDomain] at hb <;>
      omega
  right_inv := by
    intro q
    apply simplexPoint_ext <;>
      simp only <;>
      have hsum := q.sum_eq <;>
      omega

theorem card_cmoNearCentralTruncated (s : ℕ) (hs : 1 ≤ s) :
    Fintype.card (CMOTruncatedPoint (2 * s + 1) (s + 2)) =
      (s + 1).choose 2 := by
  rw [Fintype.card_congr (cmoNearCentralTruncatedEquiv s hs),
    card_simplexPoint]
  congr 1
  omega

def p6LabelToFiniteDefects :
    BenzelProblem6Kernel.MicroLabel → MicroLabel
  | .zero => .zero
  | .one => .one
  | .two => .two

def finiteDefectsLabelToP6 :
    MicroLabel → BenzelProblem6Kernel.MicroLabel
  | .zero => .zero
  | .one => .one
  | .two => .two

theorem p6_cellForOwnerAnchor_eq
    (anchor : Cell) (label : BenzelProblem6Kernel.MicroLabel) :
    BenzelProblem6Kernel.cellForOwnerAnchor anchor label =
      cellForOwnerAnchor anchor (p6LabelToFiniteDefects label) := by
  cases label <;> rfl

theorem cmoUpPhase0_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (p : SimplexPoint (2 * s + r - 1)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) label)) ↔
      inTruncatedOwnerDomain s p := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    cases label <;>
      simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
        ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
  · intro h
    simp only [inTruncatedOwnerDomain] at h
    by_cases h0 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
      ownerQ, ownerR] at h0 h1 ⊢
    omega

theorem cmoUpPhase1_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (p : SimplexPoint (2 * s + r)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) label)) ↔
      inTruncatedOwnerDomain (s + 1) p := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    cases label <;>
      simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
        ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
  · intro h
    simp only [inTruncatedOwnerDomain] at h
    by_cases h0 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
      ownerQ, ownerR] at h0 h1 ⊢
    omega

theorem cmoUpPhase2_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (p : SimplexPoint (2 * s + r + 1)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) label)) ↔
      inTruncatedOwnerDomain (s + 2) p := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    cases label <;>
      simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
        ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
  · intro h
    simp only [inTruncatedOwnerDomain] at h
    by_cases h0 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (BenzelProblem6Kernel.cellForOwnerAnchor
          (ownerQ p, ownerR p) .one)
    · exact ⟨.one, h1⟩
    refine ⟨.two, ?_⟩
    simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
      ownerQ, ownerR] at h0 h1 ⊢
    omega

inductive CMOUpVertexParameter (s r : ℕ)
  | phase0 : CMOTruncatedPoint (2 * s + r - 1) s →
      CMOUpVertexParameter s r
  | phase1 : CMOTruncatedPoint (2 * s + r) (s + 1) →
      CMOUpVertexParameter s r
  | phase2 : CMOTruncatedPoint (2 * s + r + 1) (s + 2) →
      CMOUpVertexParameter s r

def cmoUpParameterAnchor {s r : ℕ} :
    CMOUpVertexParameter s r → Cell
  | .phase0 p => (ownerQ p.1, ownerR p.1)
  | .phase1 p => (ownerQ p.1, ownerR p.1)
  | .phase2 p => (ownerQ p.1, ownerR p.1)

theorem ownerAnchor_eq_total_difference
    {N M : ℕ} (p : SimplexPoint N) (q : SimplexPoint M)
    (h : (ownerQ p, ownerR p) = (ownerQ q, ownerR q)) :
    (N : ℤ) - M = 3 * ((p.u : ℤ) - q.u) := by
  have hp := owner_phase_identity p
  have hq := owner_phase_identity q
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  omega

theorem simplexPoint_eq_of_owner_anchor
    {N : ℕ} (p q : SimplexPoint N)
    (hq : ownerQ p = ownerQ q) (hr : ownerR p = ownerR q) : p = q := by
  have hp := p.sum_eq
  have hqsum := q.sum_eq
  apply simplexPoint_ext <;>
    simp only [ownerQ, ownerR] at hq hr <;>
    omega

theorem cmoUpParameterAnchor_injective (s r : ℕ) (hs : 1 ≤ s) :
    Function.Injective (cmoUpParameterAnchor :
      CMOUpVertexParameter s r → Cell) := by
  intro left right h
  cases left with
  | phase0 p => cases right with
    | phase0 q =>
      congr 1
      apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1 q.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    | phase1 q =>
      have hdiff := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
    | phase2 q =>
      have hdiff := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
  | phase1 p => cases right with
    | phase0 q =>
      have hdiff := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
    | phase1 q =>
      congr 1
      apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1 q.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    | phase2 q =>
      have hdiff := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
  | phase2 p => cases right with
    | phase0 q =>
      have hdiff := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
    | phase1 q =>
      have hdiff := ownerAnchor_eq_total_difference p.1 q.1 h
      omega
    | phase2 q =>
      congr 1
      apply Subtype.ext
      exact simplexPoint_eq_of_owner_anchor p.1 q.1
        (congrArg Prod.fst h) (congrArg Prod.snd h)

def cmoUpParameterToAnchor
    (s r : ℕ) (hs : 1 ≤ s) :
    CMOUpVertexParameter s r →
      ↥(offsetUpAnchorFinset (2 * s + r - 1) (3 * s + 1)) :=
  fun parameter => ⟨cmoUpParameterAnchor parameter, by
    rw [mem_offsetUpAnchorFinset_iff]
    have hp := classMinusOneOffsetParameters s r hs
    rw [hp.1, hp.2]
    cases parameter with
    | phase0 p => exact (cmoUpPhase0_mem_iff s r hs p.1).2 p.2
    | phase1 p => exact (cmoUpPhase1_mem_iff s r hs p.1).2 p.2
    | phase2 p => exact (cmoUpPhase2_mem_iff s r hs p.1).2 p.2⟩

theorem cmo_exists_anchor_phase_offset (T : ℕ) (anchor : Cell) :
    ∃ c : Fin 3, IsOwnerPhase (T + c) anchor := by
  let d : ℤ := (anchor.1 - anchor.2 - (T : ℤ)) % 3
  have hd0 : 0 ≤ d := Int.emod_nonneg _ (by norm_num)
  have hd3 : d < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hcases with h | h | h
  · refine ⟨⟨0, by omega⟩, ?_⟩
    rw [IsOwnerPhase, Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
    dsimp [d] at h
    norm_num at h ⊢
    omega
  · refine ⟨⟨1, by omega⟩, ?_⟩
    rw [IsOwnerPhase, Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
    dsimp [d] at h
    norm_num at h ⊢
    omega
  · refine ⟨⟨2, by omega⟩, ?_⟩
    rw [IsOwnerPhase, Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
    dsimp [d] at h
    norm_num at h ⊢
    omega

theorem cmoUpParameterToAnchor_surjective
    (s r : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (cmoUpParameterToAnchor s r hs) := by
  intro anchor
  obtain ⟨label, hmem⟩ :=
    (mem_offsetUpAnchorFinset_iff
      (2 * s + r - 1) (3 * s + 1) anchor.1).1 anchor.2
  have hp := classMinusOneOffsetParameters s r hs
  rw [hp.1, hp.2] at hmem
  have hmemFD :
      inBenzel (2 * s + r + 1) (s + 2 * r + 1)
        (cellForOwnerAnchor anchor.1 (p6LabelToFiniteDefects label)) := by
    rw [← p6_cellForOwnerAnchor_eq]
    exact hmem
  obtain ⟨c, hphase⟩ :=
    cmo_exists_anchor_phase_offset (2 * s + r - 1) anchor.1
  rcases c with ⟨c, hc⟩
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hcases with hcase | hcase | hcase
  · subst c
    have hwide :
        inBenzel ((2 * s + r - 1) + 2) (s + 2 * r + 1)
          (cellForOwnerAnchor anchor.1 (p6LabelToFiniteDefects label)) := by
      rw [hp.1]
      exact hmemFD
    obtain ⟨p, hq, hr⟩ := phase_anchor_has_simplex
      (2 * s + r - 1) (s + 2 * r + 1) anchor.1
      (p6LabelToFiniteDefects label) hphase hwide
    have hbound : inTruncatedOwnerDomain s p :=
      (cmoUpPhase0_mem_iff s r hs p).1 ⟨label, by
        rw [p6_cellForOwnerAnchor_eq, hq, hr]
        exact hmemFD⟩
    refine ⟨.phase0 ⟨p, hbound⟩, Subtype.ext ?_⟩
    exact Prod.ext hq hr
  · subst c
    have ht : 2 * s + r - 1 + 1 = 2 * s + r := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase
    rw [ht] at hphase
    have hwide :
        inBenzel ((2 * s + r) + 2) (s + 2 * r + 1)
          (cellForOwnerAnchor anchor.1 (p6LabelToFiniteDefects label)) := by
      dsimp [inBenzel] at hmemFD ⊢
      omega
    obtain ⟨p, hq, hr⟩ := phase_anchor_has_simplex
      (2 * s + r) (s + 2 * r + 1) anchor.1
      (p6LabelToFiniteDefects label) hphase hwide
    have hbound : inTruncatedOwnerDomain (s + 1) p :=
      (cmoUpPhase1_mem_iff s r hs p).1 ⟨label, by
        rw [p6_cellForOwnerAnchor_eq, hq, hr]
        exact hmemFD⟩
    refine ⟨.phase1 ⟨p, hbound⟩, Subtype.ext ?_⟩
    exact Prod.ext hq hr
  · subst c
    have ht : 2 * s + r - 1 + 2 = 2 * s + r + 1 := by omega
    simp only [Fin.coe_ofNat_eq_mod] at hphase
    rw [ht] at hphase
    have hwide :
        inBenzel ((2 * s + r + 1) + 2) (s + 2 * r + 1)
          (cellForOwnerAnchor anchor.1 (p6LabelToFiniteDefects label)) := by
      dsimp [inBenzel] at hmemFD ⊢
      omega
    obtain ⟨p, hq, hr⟩ := phase_anchor_has_simplex
      (2 * s + r + 1) (s + 2 * r + 1) anchor.1
      (p6LabelToFiniteDefects label) hphase hwide
    have hbound : inTruncatedOwnerDomain (s + 2) p :=
      (cmoUpPhase2_mem_iff s r hs p).1 ⟨label, by
        rw [p6_cellForOwnerAnchor_eq, hq, hr]
        exact hmemFD⟩
    refine ⟨.phase2 ⟨p, hbound⟩, Subtype.ext ?_⟩
    exact Prod.ext hq hr

abbrev CMOUpVertexParameterSum (s r : ℕ) :=
  CMOTruncatedPoint (2 * s + r - 1) s ⊕
    (CMOTruncatedPoint (2 * s + r) (s + 1) ⊕
      CMOTruncatedPoint (2 * s + r + 1) (s + 2))

def cmoUpVertexParameterEquivSum (s r : ℕ) :
    CMOUpVertexParameter s r ≃ CMOUpVertexParameterSum s r where
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

noncomputable def cmoUpVertexParameterFintype (s r : ℕ) :
    Fintype (CMOUpVertexParameter s r) :=
  Fintype.ofEquiv (CMOUpVertexParameterSum s r)
    (cmoUpVertexParameterEquivSum s r).symm

noncomputable def cmoUpVertexParameterEquiv
    (s r : ℕ) (hs : 1 ≤ s) :
    CMOUpVertexParameter s r ≃
      ↥(offsetUpAnchorFinset (2 * s + r - 1) (3 * s + 1)) :=
  Equiv.ofBijective (cmoUpParameterToAnchor s r hs)
    ⟨by
      intro left right h
      exact cmoUpParameterAnchor_injective s r hs
        (congrArg Subtype.val h),
      cmoUpParameterToAnchor_surjective s r hs⟩

theorem card_cmoUpVertexParameter (s r : ℕ) :
    letI := cmoUpVertexParameterFintype s r
    Fintype.card (CMOUpVertexParameter s r) =
      Fintype.card (CMOTruncatedPoint (2 * s + r - 1) s) +
        Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) +
          Fintype.card (CMOTruncatedPoint (2 * s + r + 1) (s + 2)) := by
  letI := cmoUpVertexParameterFintype s r
  rw [Fintype.card_congr (cmoUpVertexParameterEquivSum s r),
    Fintype.card_sum, Fintype.card_sum]
  omega

theorem card_cmoUpAnchorFinset_as_truncated
    (s r : ℕ) (hs : 1 ≤ s) :
    (offsetUpAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      Fintype.card (CMOTruncatedPoint (2 * s + r - 1) s) +
      Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) +
          Fintype.card (CMOTruncatedPoint (2 * s + r + 1) (s + 2)) := by
  letI := cmoUpVertexParameterFintype s r
  rw [← Fintype.card_coe]
  rw [← Fintype.card_congr (cmoUpVertexParameterEquiv s r hs),
    card_cmoUpVertexParameter]

theorem twice_choose_two (n : ℕ) : n.choose 2 * 2 = n * (n - 1) := by
  simpa using Nat.choose_succ_right_eq n 1

theorem card_cmoUpAnchorFinset_r_zero
    (s : ℕ) (hs : 1 ≤ s) :
    (offsetUpAnchorFinset (2 * s + 0 - 1) (3 * s + 1)).card =
      (2 * s + 1).choose 2 - 3 * s.choose 2 +
        (s + 2).choose 2 + (s + 1).choose 2 := by
  rw [card_cmoUpAnchorFinset_as_truncated s 0 hs]
  simp only [Nat.add_zero]
  rw [card_cmoTruncatedPoint_of_room (2 * s - 1) s hs (by omega),
    card_cmoCentralTruncated s hs,
    card_cmoNearCentralTruncated s hs]
  rw [show 2 * s - 1 + 2 = 2 * s + 1 by omega]

theorem card_cmoUpAnchorFinset_r_one
    (s : ℕ) (hs : 1 ≤ s) :
    (offsetUpAnchorFinset (2 * s + 1 - 1) (3 * s + 1)).card =
      (2 * s + 2).choose 2 - 3 * s.choose 2 +
        ((2 * s + 3).choose 2 - 3 * (s + 1).choose 2) +
          (s + 3).choose 2 := by
  rw [card_cmoUpAnchorFinset_as_truncated s 1 hs]
  rw [card_cmoTruncatedPoint_of_room (2 * s + 1 - 1) s hs (by omega),
    card_cmoTruncatedPoint_of_room (2 * s + 1) (s + 1) (by omega) (by omega)]
  have hcentral := card_cmoCentralTruncated (s + 1) (by omega)
  have hthird :
      Fintype.card (CMOTruncatedPoint (2 * s + 1 + 1) (s + 2)) =
        (s + 3).choose 2 := by
    simpa only [show 2 * (s + 1) = 2 * s + 1 + 1 by omega,
      show s + 1 + 2 = s + 3 by omega] using hcentral
  rw [hthird]
  rw [show 2 * s + 1 - 1 + 2 = 2 * s + 2 by omega,
    show 2 * s + 1 + 2 = 2 * s + 3 by omega]

theorem card_cmoUpAnchorFinset_r_ge_two
    (s r : ℕ) (hs : 1 ≤ s) (hr : 2 ≤ r) :
    (offsetUpAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      (2 * s + r + 1).choose 2 - 3 * s.choose 2 +
        ((2 * s + r + 2).choose 2 - 3 * (s + 1).choose 2) +
          ((2 * s + r + 3).choose 2 - 3 * (s + 2).choose 2) := by
  rw [card_cmoUpAnchorFinset_as_truncated s r hs,
    card_cmoTruncatedPoint_of_room (2 * s + r - 1) s hs (by omega),
    card_cmoTruncatedPoint_of_room (2 * s + r) (s + 1) (by omega) (by omega),
    card_cmoTruncatedPoint_of_room (2 * s + r + 1) (s + 2) (by omega) (by omega)]
  rw [show 2 * s + r - 1 + 2 = 2 * s + r + 1 by omega]

theorem twice_choose_two_int (n : ℕ) (hn : 1 ≤ n) :
    2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  rw [← Nat.cast_one, ← Nat.cast_sub hn]
  exact_mod_cast (by simpa [mul_comm] using twice_choose_two n)

theorem twice_card_cmoUpAnchorFinset_r_zero
    (s : ℕ) (hs : 1 ≤ s) :
    2 * (offsetUpAnchorFinset (2 * s + 0 - 1) (3 * s + 1)).card =
      3 * s * s + 9 * s + 2 := by
  rw [card_cmoUpAnchorFinset_r_zero s hs]
  have hS := twice_choose_two_int s hs
  have hS1 := twice_choose_two_int (s + 1) (by omega)
  have hS2 := twice_choose_two_int (s + 2) (by omega)
  have hA := twice_choose_two_int (2 * s + 1) (by omega)
  push_cast at hS hS1 hS2 hA
  have hleZ : 3 * (s.choose 2 : ℤ) ≤ ((2 * s + 1).choose 2 : ℤ) := by
    nlinarith
  have hle : 3 * s.choose 2 ≤ (2 * s + 1).choose 2 := by
    exact_mod_cast hleZ
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hle]
  push_cast
  nlinarith

theorem twice_card_cmoUpAnchorFinset_r_one
    (s : ℕ) (hs : 1 ≤ s) :
    2 * (offsetUpAnchorFinset (2 * s + 1 - 1) (3 * s + 1)).card =
      3 * s * s + 21 * s + 14 := by
  rw [card_cmoUpAnchorFinset_r_one s hs]
  have hS := twice_choose_two_int s hs
  have hS1 := twice_choose_two_int (s + 1) (by omega)
  have hS3 := twice_choose_two_int (s + 3) (by omega)
  have hA := twice_choose_two_int (2 * s + 2) (by omega)
  have hB := twice_choose_two_int (2 * s + 3) (by omega)
  push_cast at hS hS1 hS3 hA hB
  have hleAZ : 3 * (s.choose 2 : ℤ) ≤ ((2 * s + 2).choose 2 : ℤ) := by
    nlinarith
  have hleBZ : 3 * ((s + 1).choose 2 : ℤ) ≤
      ((2 * s + 3).choose 2 : ℤ) := by
    nlinarith
  have hleA : 3 * s.choose 2 ≤ (2 * s + 2).choose 2 := by
    exact_mod_cast hleAZ
  have hleB : 3 * (s + 1).choose 2 ≤ (2 * s + 3).choose 2 := by
    exact_mod_cast hleBZ
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hleA, Nat.cast_sub hleB]
  push_cast
  nlinarith

theorem twice_card_cmoUpAnchorFinset_r_ge_two
    (s r : ℕ) (hs : 1 ≤ s) (hr : 2 ≤ r) :
    2 * (offsetUpAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      3 * s * s + 3 * r * r + 12 * s * r + 9 * s + 9 * r + 2 := by
  rw [card_cmoUpAnchorFinset_r_ge_two s r hs hr]
  have hS := twice_choose_two_int s hs
  have hS1 := twice_choose_two_int (s + 1) (by omega)
  have hS2 := twice_choose_two_int (s + 2) (by omega)
  have hA := twice_choose_two_int (2 * s + r + 1) (by omega)
  have hB := twice_choose_two_int (2 * s + r + 2) (by omega)
  have hC := twice_choose_two_int (2 * s + r + 3) (by omega)
  push_cast at hS hS1 hS2 hA hB hC
  have hleAZ : 3 * (s.choose 2 : ℤ) ≤
      ((2 * s + r + 1).choose 2 : ℤ) := by
    nlinarith
  have hleBZ : 3 * ((s + 1).choose 2 : ℤ) ≤
      ((2 * s + r + 2).choose 2 : ℤ) := by
    nlinarith
  have hleCZ : 3 * ((s + 2).choose 2 : ℤ) ≤
      ((2 * s + r + 3).choose 2 : ℤ) := by
    nlinarith
  have hleA : 3 * s.choose 2 ≤ (2 * s + r + 1).choose 2 := by
    exact_mod_cast hleAZ
  have hleB : 3 * (s + 1).choose 2 ≤ (2 * s + r + 2).choose 2 := by
    exact_mod_cast hleBZ
  have hleC : 3 * (s + 2).choose 2 ≤ (2 * s + r + 3).choose 2 := by
    exact_mod_cast hleCZ
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hleA, Nat.cast_sub hleB, Nat.cast_sub hleC]
  push_cast
  nlinarith

theorem twice_card_cmoUpAnchorFinset
    (s r : ℕ) (hs : 1 ≤ s) :
    2 * (offsetUpAnchorFinset (2 * s + r - 1) (3 * s + 1)).card =
      3 * s * s + 3 * r * r + 12 * s * r + 9 * s + 9 * r + 2 := by
  by_cases hr0 : r = 0
  · subst r
    simpa using twice_card_cmoUpAnchorFinset_r_zero s hs
  by_cases hr1 : r = 1
  · subst r
    have h := twice_card_cmoUpAnchorFinset_r_one s hs
    omega
  exact twice_card_cmoUpAnchorFinset_r_ge_two s r hs (by omega)

end FiniteDefects
