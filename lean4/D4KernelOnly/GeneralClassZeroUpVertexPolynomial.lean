import D4KernelOnly.GeneralClassZeroUpVertexCard

/-! # Cached polynomial simplification for the class-zero up-vertex count -/

namespace FiniteDefects

set_option maxHeartbeats 800000

theorem twice_card_czUpAnchor
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    2 * (offsetUpAnchorFinset (2 * s + r - 2) (3 * s)).card =
      3 * s * s + 3 * r * r + 12 * s * r + 3 * s + 3 * r - 4 := by
  by_cases hr1 : r = 1
  · subst r
    rw [card_czUpAnchor_r_one s hs]
    have hS := twice_choose_two_int s hs
    have hS1 := twice_choose_two_int (s + 1) (by omega)
    have hS2 := twice_choose_two_int (s + 2) (by omega)
    have hA := twice_choose_two_int (2 * s + 1) (by omega)
    have hC := twice_choose_two_int (2 * s + 3) (by omega)
    push_cast at hS hS1 hS2 hA hC
    have hleA : 3 * s.choose 2 ≤ (2 * s + 1).choose 2 := by
      exact_mod_cast (show 3 * (s.choose 2 : ℤ) ≤
        ((2 * s + 1).choose 2 : ℤ) by nlinarith)
    have hleC : 3 * (s + 1).choose 2 ≤ (2 * s + 3).choose 2 := by
      exact_mod_cast (show 3 * ((s + 1).choose 2 : ℤ) ≤ ((2 * s + 3).choose 2 : ℤ) by nlinarith)
    have hthree : 3 ≤ (2 * s + 3).choose 2 - 3 * (s + 1).choose 2 := by
      have hz : (3 : ℤ) ≤ ((2 * s + 3).choose 2 : ℤ) -
          3 * ((s + 1).choose 2 : ℤ) := by nlinarith
      have hz' : (3 : ℤ) ≤
          (((2 * s + 3).choose 2 - 3 * (s + 1).choose 2 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hleC]
        push_cast
        exact hz
      exact_mod_cast hz'
    have htarget :
        3 * s * s + 3 * 1 * 1 + 12 * s * 1 + 3 * s + 3 * 1 - 4 =
          3 * s * s + 15 * s + 2 := by omega
    rw [htarget]
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [Nat.cast_sub hleA, Nat.cast_sub hthree, Nat.cast_sub hleC]
    push_cast
    nlinarith
  · rw [card_czUpAnchor_r_ge_two s r hs (by omega)]
    have hS := twice_choose_two_int s hs
    have hS1 := twice_choose_two_int (s + 1) (by omega)
    have hA := twice_choose_two_int (2 * s + r) (by omega)
    have hB := twice_choose_two_int (2 * s + r + 1) (by omega)
    have hC := twice_choose_two_int (2 * s + r + 2) (by omega)
    push_cast at hS hS1 hA hB hC
    have hleA : 3 * s.choose 2 ≤ (2 * s + r).choose 2 := by
      exact_mod_cast (show 3 * (s.choose 2 : ℤ) ≤
        ((2 * s + r).choose 2 : ℤ) by nlinarith)
    have hleB : 3 * (s + 1).choose 2 ≤ (2 * s + r + 1).choose 2 := by
      exact_mod_cast (show 3 * ((s + 1).choose 2 : ℤ) ≤
        ((2 * s + r + 1).choose 2 : ℤ) by nlinarith)
    have hleC : 3 * (s + 1).choose 2 ≤ (2 * s + r + 2).choose 2 := by
      exact_mod_cast (show 3 * ((s + 1).choose 2 : ℤ) ≤
        ((2 * s + r + 2).choose 2 : ℤ) by nlinarith)
    have hthree : 3 ≤ (2 * s + r + 2).choose 2 - 3 * (s + 1).choose 2 := by
      have hz : (3 : ℤ) ≤ ((2 * s + r + 2).choose 2 : ℤ) -
          3 * ((s + 1).choose 2 : ℤ) := by nlinarith
      have hz' : (3 : ℤ) ≤
          (((2 * s + r + 2).choose 2 - 3 * (s + 1).choose 2 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hleC]
        push_cast
        exact hz
      exact_mod_cast hz'
    have hsmall : 4 ≤ 3 * s + 3 * r := by omega
    have htarget :
        3 * s * s + 3 * r * r + 12 * s * r + 3 * s + 3 * r - 4 =
          3 * s * s + 3 * r * r + 12 * s * r + (3 * s + 3 * r - 4) := by
      omega
    rw [htarget]
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [Nat.cast_sub hleA, Nat.cast_sub hleB,
      Nat.cast_sub hthree, Nat.cast_sub hleC, Nat.cast_sub hsmall]
    push_cast
    nlinarith

end FiniteDefects
