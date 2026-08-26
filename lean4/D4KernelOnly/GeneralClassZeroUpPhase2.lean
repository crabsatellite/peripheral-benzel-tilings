import D4KernelOnly.GeneralClassZeroArea
import D4KernelOnly.GeneralCellVertexCarrier

/-! # Cached third up-vertex phase and its three corner exclusions -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option maxHeartbeats 800000

def czUpException0 (s r : ℕ) : SimplexPoint (2 * s + r) where
  u := 0; v := s; w := s + r; sum_eq := by omega
def czUpException1 (s r : ℕ) : SimplexPoint (2 * s + r) where
  u := s; v := s + r; w := 0; sum_eq := by omega
def czUpException2 (s r : ℕ) : SimplexPoint (2 * s + r) where
  u := s + r; v := 0; w := s; sum_eq := by omega

def czUpPhase2Exceptions (s r : ℕ) : Finset (SimplexPoint (2 * s + r)) :=
  {czUpException0 s r, czUpException1 s r, czUpException2 s r}

theorem czUpPhase2_mem_iff
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (p : SimplexPoint (2 * s + r)) :
    (∃ label : BenzelProblem6Kernel.MicroLabel,
      inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) label)) ↔
      inTruncatedOwnerDomain (s + 1) p ∧ p ∉ czUpPhase2Exceptions s r := by
  have hsum := p.sum_eq
  constructor
  · rintro ⟨label, h⟩
    constructor
    · cases label <;>
        simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
          ownerQ, ownerR, inTruncatedOwnerDomain] at h ⊢ <;> omega
    · intro hex
      simp only [czUpPhase2Exceptions, Finset.mem_insert,
        Finset.mem_singleton] at hex
      rcases hex with hp | hp | hp <;> subst p <;>
        cases label <;>
        simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
          ownerQ, ownerR, czUpException0, czUpException1,
          czUpException2] at h <;> omega
  · rintro ⟨hdom, hallowed⟩
    simp only [inTruncatedOwnerDomain] at hdom
    by_cases h0 : inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) .zero)
    · exact ⟨.zero, h0⟩
    by_cases h1 : inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) .one)
    · exact ⟨.one, h1⟩
    by_cases h2 : inBenzel (2 * s + r) (s + 2 * r)
        (BenzelProblem6Kernel.cellForOwnerAnchor (ownerQ p, ownerR p) .two)
    · exact ⟨.two, h2⟩
    exfalso
    apply hallowed
    simp only [czUpPhase2Exceptions, Finset.mem_insert, Finset.mem_singleton]
    simp [inBenzel, BenzelProblem6Kernel.cellForOwnerAnchor,
      ownerQ, ownerR] at h0 h1 h2
    have hcases :
        (p.u = 0 ∧ p.v = s ∧ p.w = s + r) ∨
        (p.u = s ∧ p.v = s + r ∧ p.w = 0) ∨
        (p.u = s + r ∧ p.v = 0 ∧ p.w = s) := by omega
    rcases hcases with h | h | h
    · left; apply simplexPoint_ext <;> simp [czUpException0] <;> omega
    · right; left; apply simplexPoint_ext <;> simp [czUpException1] <;> omega
    · right; right; apply simplexPoint_ext <;> simp [czUpException2] <;> omega

end FiniteDefects
