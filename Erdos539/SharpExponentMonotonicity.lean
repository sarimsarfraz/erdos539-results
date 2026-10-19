/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpExponents

namespace Erdos539Geometry

theorem combineExponent_mono_left {a a' b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ a') :
    combineExponent a b ≤ combineExponent a' b := by
  unfold combineExponent
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

theorem sharpExponent_succ_le (d : ℕ) : sharpExponent (d + 1) ≤ sharpExponent d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d ≤ 1
    · rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
      · norm_num
      · simpa only [sharpExponent_one] using (sharpExponent_bounds 2).2
    obtain ⟨p, s, hp, hs, he, hmin⟩ := sharpExponent_attained (by omega : 2 ≤ d)
    have hip := ih p (by omega)
    have hsplit := sharpExponent_le_split (show 0 < p + 1 by omega) hs
    have hdim : p + 1 + s = d + 1 := by omega
    rw [hdim] at hsplit
    apply hsplit.trans
    rw [hmin]
    exact combineExponent_mono_left (sharpExponent_pos (p + 1)).le (sharpExponent_pos s).le hip

theorem sharpExponent_antitone : Antitone sharpExponent :=
  antitone_nat_of_succ_le sharpExponent_succ_le

theorem sharpExponent_le_parts {p s : ℕ} :
    sharpExponent (p + s) ≤ sharpExponent p ∧ sharpExponent (p + s) ≤ sharpExponent s :=
  ⟨sharpExponent_antitone (Nat.le_add_right p s), sharpExponent_antitone (Nat.le_add_left s p)⟩

end Erdos539Geometry
