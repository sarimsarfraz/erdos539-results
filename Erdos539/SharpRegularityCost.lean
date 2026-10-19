/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.InductionEstimates
import Erdos539.SharpExponents

namespace Erdos539Geometry
noncomputable section

/-- The sharp fiber-regularity cost used in the manuscript. -/
def sharpRegularityCost (d : ℕ) : ℝ :=
  if d = 1 then 0 else (1 + regularityCost d) / 2

@[simp] theorem sharpRegularityCost_one : sharpRegularityCost 1 = 0 := by
  simp [sharpRegularityCost]

theorem sharpRegularityCost_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ sharpRegularityCost d := by
  unfold sharpRegularityCost
  split_ifs
  · exact le_rfl
  · have h := regularityCost_nonneg hd
    positivity

theorem one_le_sharpRegularityCost {d : ℕ} (hd : 2 ≤ d) : 1 ≤ sharpRegularityCost d := by
  rw [sharpRegularityCost, if_neg (by omega)]
  linarith [one_le_regularityCost hd]

theorem sharpRegularityCost_mono {p s : ℕ} (hp : 0 < p) (hps : p ≤ s) :
    sharpRegularityCost p ≤ sharpRegularityCost s := by
  by_cases hp1 : p = 1
  · rw [hp1, sharpRegularityCost_one]
    exact sharpRegularityCost_nonneg (hp.trans_le hps)
  have hs1 : s ≠ 1 := by omega
  rw [sharpRegularityCost, if_neg hp1, sharpRegularityCost, if_neg hs1]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h := Real.log_le_log hp0 (show (p : ℝ) ≤ s by exact_mod_cast hps)
  have hcost := div_le_div_of_nonneg_right h log_two_pos.le
  change regularityCost p ≤ regularityCost s at hcost
  linarith

/-- The regularity loss closes for every nonempty split, including one-dimensional children. -/
theorem sharpRegularityCost_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s)
    {t : ℝ} (ht : 1 ≤ t) :
    (sharpRegularityCost p + sharpRegularityCost s + t) / (1 + t) ≤ sharpRegularityCost (p + s) := by
  have hm : 1 ≤ sharpRegularityCost (p + s) := one_le_sharpRegularityCost (by omega)
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).mpr
  by_cases hp1 : p = 1
  · rw [hp1, sharpRegularityCost_one, zero_add]
    have hmono := sharpRegularityCost_mono hs (Nat.le_add_left s 1)
    have hm' : 1 ≤ sharpRegularityCost (1 + s) := hp1 ▸ hm
    nlinarith
  by_cases hs1 : s = 1
  · rw [hs1, sharpRegularityCost_one, add_zero]
    have hmono := sharpRegularityCost_mono hp (Nat.le_add_right p 1)
    have hm' : 1 ≤ sharpRegularityCost (p + 1) := hs1 ▸ hm
    nlinarith
  have hmne : p + s ≠ 1 := by omega
  have hsum := regularityCost_sum_le hp hs
  have hlog := one_le_regularityCost (show 2 ≤ p + s by omega)
  rw [sharpRegularityCost, if_neg hp1, sharpRegularityCost, if_neg hs1,
    sharpRegularityCost, if_neg hmne]
  nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr ht)]

theorem sharpRegularityCost_le_twice {d : ℕ} (hd : 0 < d) : sharpRegularityCost d ≤ 2 * d := by
  by_cases hd1 : d = 1
  · rw [hd1, sharpRegularityCost_one]
    norm_num
  rw [sharpRegularityCost, if_neg hd1]
  have h := regularityCost_le_twice hd
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem sharp_induction_constant_budget {p s : ℕ} (hp : 0 < p) (hs : 0 < s)
    {t : ℝ} (ht : 1 ≤ t) :
    8 * ((p + s : ℕ) : ℝ) + sharpRegularityCost p + sharpRegularityCost s +
      (((p + s : ℕ) : ℝ) + 3) * t ≤ 8 * ((p + s : ℕ) : ℝ) * (1 + t) := by
  have hpc := sharpRegularityCost_le_twice hp
  have hsc := sharpRegularityCost_le_twice hs
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ p + s - 2 by linarith) (sub_nonneg.mpr ht)]

/-- Real-valued wrappers retain the exact rational minimizing-split recursion. -/
def sharpExponentReal (d : ℕ) : ℝ := sharpExponent d

theorem sharpExponentReal_pos {d : ℕ} (_hd : 0 < d) : 0 < sharpExponentReal d := by
  dsimp only [sharpExponentReal]
  exact_mod_cast sharpExponent_pos d

theorem sharpExponentReal_le_one {d : ℕ} (_hd : 0 < d) : sharpExponentReal d ≤ 1 := by
  dsimp only [sharpExponentReal]
  exact_mod_cast (sharpExponent_bounds d).2

@[simp] theorem sharpExponentReal_one : sharpExponentReal 1 = 1 := by
  norm_num [sharpExponentReal]

theorem one_le_sharpExponentReal_sum {p s : ℕ} (_hp : 0 < p) (_hs : 0 < s) :
    1 ≤ sharpExponentReal p + sharpExponentReal s := by
  have hp : (1 : ℝ) / 2 ≤ sharpExponentReal p := by
    dsimp only [sharpExponentReal]
    have h : ((1 / 2 : ℚ) : ℝ) ≤ (sharpExponent p : ℝ) := by exact_mod_cast (sharpExponent_bounds p).1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    exact h
  have hs : (1 : ℝ) / 2 ≤ sharpExponentReal s := by
    dsimp only [sharpExponentReal]
    have h : ((1 / 2 : ℚ) : ℝ) ≤ (sharpExponent s : ℝ) := by exact_mod_cast (sharpExponent_bounds s).1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    exact h
  linarith

theorem sharpExponentReal_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    sharpExponentReal (p + s) ≤
      (sharpExponentReal p + sharpExponentReal s) / (1 + sharpExponentReal p + sharpExponentReal s) := by
  have h : (sharpExponent (p + s) : ℝ) ≤
      (combineExponent (sharpExponent p) (sharpExponent s) : ℝ) := by
    exact_mod_cast sharpExponent_le_split hp hs
  rw [combineExponent] at h
  push_cast at h
  exact h

end
end Erdos539Geometry
