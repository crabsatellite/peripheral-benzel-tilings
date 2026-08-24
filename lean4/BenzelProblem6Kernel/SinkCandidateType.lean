import BenzelProblem6Kernel.ActiveOwnerCoverage

/-!
# Incoming-label type of the unique no-outgoing active owner
-/

namespace BenzelProblem6Kernel

noncomputable def incomingLabelFinset
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3)) :
    Finset MicroLabel :=
  ((literalDirectedEdges hstone tiling).filter fun edge => edge.target = p).image
    (fun edge => edge.boneClass.label)

noncomputable def presentLabelFinset {m : ℕ} (p : SimplexPoint (m + 3)) :
    Finset MicroLabel :=
  Finset.univ.filter fun label => inPeripheralBenzel (m + 5) (ownerCell p label)

theorem mem_incomingLabelFinset_iff_present
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3))
    (hpActive : p ∈ activeOwnerFinset hstone tiling)
    (hpNoOut : p ∉ activeOwnerEdgeSourceFinset hstone tiling)
    (label : MicroLabel) :
    label ∈ incomingLabelFinset hstone tiling p ↔
      label ∈ presentLabelFinset p := by
  classical
  constructor
  · intro hlabel
    simp only [incomingLabelFinset, Finset.mem_image, Finset.mem_filter] at hlabel
    obtain ⟨edge, ⟨hedge, htarget⟩, hedgeLabel⟩ := hlabel
    simp only [presentLabelFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmem := literalDirectedEdge_target_cell_mem edge
    simpa [htarget, hedgeLabel] using hmem
  · intro hlabel
    simp only [presentLabelFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hlabel
    obtain ⟨edge, hedge, hrole⟩ :=
      active_owner_present_label_role hstone tiling p hpActive label hlabel
    rcases hrole with hsource | htarget
    · exfalso
      apply hpNoOut
      simp only [activeOwnerEdgeSourceFinset, Finset.mem_image]
      exact ⟨edge, hedge, hsource.1⟩
    · simp only [incomingLabelFinset, Finset.mem_image, Finset.mem_filter]
      exact ⟨edge, ⟨hedge, htarget.1⟩, htarget.2⟩

theorem incomingLabelFinset_eq_present
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3))
    (hpActive : p ∈ activeOwnerFinset hstone tiling)
    (hpNoOut : p ∉ activeOwnerEdgeSourceFinset hstone tiling) :
    incomingLabelFinset hstone tiling p = presentLabelFinset p := by
  ext label
  exact mem_incomingLabelFinset_iff_present hstone tiling p hpActive hpNoOut label

theorem literalIndegree_eq_presentLabelCard_of_noOut
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3))
    (hpActive : p ∈ activeOwnerFinset hstone tiling)
    (hpNoOut : p ∉ activeOwnerEdgeSourceFinset hstone tiling) :
    literalIndegree hstone tiling p = (presentLabelFinset p).card := by
  classical
  have hinj := incoming_label_injective hstone tiling p
  calc
    literalIndegree hstone tiling p =
        (((literalDirectedEdges hstone tiling).filter fun edge => edge.target = p).image
          (fun edge => edge.boneClass.label)).card := by
      rw [literalIndegree, Finset.card_image_of_injOn hinj]
    _ = (presentLabelFinset p).card := by
      rw [← incomingLabelFinset, incomingLabelFinset_eq_present hstone tiling p
        hpActive hpNoOut]

theorem full_owner_presentLabel_card {m : ℕ} (p : SimplexPoint (m + 3))
    (hu : p.u < m + 3) (hv : p.v < m + 3) (hw : p.w < m + 3) :
    (presentLabelFinset p).card = 3 := by
  classical
  have hzero := (owner_zero_mem_iff (n := m + 5) (by omega) p).2 hv
  have hone := (owner_one_mem_iff (n := m + 5) (by omega) p).2 hw
  have htwo := (owner_two_mem_iff (n := m + 5) (by omega) p).2 hu
  have huniv : presentLabelFinset p = Finset.univ := by
    ext label
    rcases label <;> simp [presentLabelFinset, hzero, hone, htwo]
  rw [huniv]
  decide

theorem sourceZero_presentLabel_card (m : ℕ) :
    (presentLabelFinset (sourceZero (m + 3))).card = 2 := by
  classical
  have hmissing := (owner_zero_missing_iff (n := m + 5) (by omega)
    (sourceZero (m + 3))).2 (by simp [sourceZero])
  have hone := (owner_one_mem_iff (n := m + 5) (by omega)
    (sourceZero (m + 3))).2 (by simp [sourceZero])
  have htwo := (owner_two_mem_iff (n := m + 5) (by omega)
    (sourceZero (m + 3))).2 (by simp [sourceZero])
  have heq : presentLabelFinset (sourceZero (m + 3)) = {.one, .two} := by
    ext label
    rcases label <;> simp [presentLabelFinset, hmissing, hone, htwo]
  rw [heq]
  decide

theorem sourceOne_presentLabel_card (m : ℕ) :
    (presentLabelFinset (sourceOne (m + 3))).card = 2 := by
  classical
  have hzero := (owner_zero_mem_iff (n := m + 5) (by omega)
    (sourceOne (m + 3))).2 (by simp [sourceOne])
  have hmissing := (owner_one_missing_iff (n := m + 5) (by omega)
    (sourceOne (m + 3))).2 (by simp [sourceOne])
  have htwo := (owner_two_mem_iff (n := m + 5) (by omega)
    (sourceOne (m + 3))).2 (by simp [sourceOne])
  have heq : presentLabelFinset (sourceOne (m + 3)) = {.zero, .two} := by
    ext label
    rcases label <;> simp [presentLabelFinset, hzero, hmissing, htwo]
  rw [heq]
  decide

theorem sourceTwo_presentLabel_card (m : ℕ) :
    (presentLabelFinset (sourceTwo (m + 3))).card = 2 := by
  classical
  have hzero := (owner_zero_mem_iff (n := m + 5) (by omega)
    (sourceTwo (m + 3))).2 (by simp [sourceTwo])
  have hone := (owner_one_mem_iff (n := m + 5) (by omega)
    (sourceTwo (m + 3))).2 (by simp [sourceTwo])
  have hmissing := (owner_two_missing_iff (n := m + 5) (by omega)
    (sourceTwo (m + 3))).2 (by simp [sourceTwo])
  have heq : presentLabelFinset (sourceTwo (m + 3)) = {.zero, .one} := by
    ext label
    rcases label <;> simp [presentLabelFinset, hzero, hone, hmissing]
  rw [heq]
  decide

theorem noOutgoing_active_owner_sink_type
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3))
    (hpActive : p ∈ activeOwnerFinset hstone tiling)
    (hpNoOut : p ∉ activeOwnerEdgeSourceFinset hstone tiling) :
    (p = sourceZero (m + 3) ∨ p = sourceOne (m + 3) ∨
      p = sourceTwo (m + 3)) ∧ literalIndegree hstone tiling p = 2 ∨
    (p.u < m + 3 ∧ p.v < m + 3 ∧ p.w < m + 3) ∧
      literalIndegree hstone tiling p = 3 := by
  have hdegree := literalIndegree_eq_presentLabelCard_of_noOut hstone tiling p
    hpActive hpNoOut
  rcases simplex_corner_or_full (t := m + 3) (by omega) p with h0 | h1 | h2 | hfull
  · left
    refine ⟨Or.inl h0, ?_⟩
    rw [hdegree, h0, sourceZero_presentLabel_card]
  · left
    refine ⟨Or.inr (Or.inl h1), ?_⟩
    rw [hdegree, h1, sourceOne_presentLabel_card]
  · left
    refine ⟨Or.inr (Or.inr h2), ?_⟩
    rw [hdegree, h2, sourceTwo_presentLabel_card]
  · right
    refine ⟨hfull, ?_⟩
    rw [hdegree, full_owner_presentLabel_card p hfull.1 hfull.2.1 hfull.2.2]

end BenzelProblem6Kernel
