/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.UniformExponents

namespace Erdos539Geometry
noncomputable section

@[simp] theorem uniformExponent_one : uniformExponent 1 = 1 := by norm_num [uniformExponent]
@[simp] theorem regularityCost_one : regularityCost 1 = 0 := by simp [regularityCost]

theorem one_le_uniformExponent_sum {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    1 ≤ uniformExponent p + uniformExponent s := by
  have ha := uniformExponent_ge_half_add hp
  have hb := uniformExponent_ge_half_add hs
  have hpa : (0 : ℝ) ≤ 1 / (4 * (p : ℝ)) := by positivity
  have hsa : (0 : ℝ) ≤ 1 / (4 * (s : ℝ)) := by positivity
  linarith

theorem uniformExponent_sum_le_two {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    uniformExponent p + uniformExponent s ≤ 2 := by
  linarith [uniformExponent_le_one hp, uniformExponent_le_one hs]

theorem regularityCost_sum_le {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    regularityCost p + regularityCost s ≤ 2 * regularityCost (p + s) - 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hm0 : (0 : ℝ) < (p + s : ℕ) := by positivity
  have hsq : (2 * (p : ℝ)) * (2 * (s : ℝ)) ≤ ((p + s : ℕ) : ℝ) * (p + s : ℕ) := by
    push_cast
    nlinarith [sq_nonneg ((p : ℝ) - s)]
  have hlog := Real.log_le_log (mul_pos (mul_pos (by norm_num) hp0)
    (mul_pos (by norm_num) hs0)) hsq
  rw [Real.log_mul (by positivity : 2 * (p : ℝ) ≠ 0) (by positivity : 2 * (s : ℝ) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp0.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs0.ne', Real.log_mul hm0.ne' hm0.ne'] at hlog
  dsimp only [regularityCost]
  rw [← add_div]
  calc
    _ ≤ (2 * Real.log ((p + s : ℕ) : ℝ) - 2 * Real.log 2) / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) log_two_pos.le
    _ = _ := by field_simp

/-- The logarithmic regularity loss closes for every nonempty binary split. -/
theorem regularityCost_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s)
    {t : ℝ} (ht : 1 ≤ t) :
    (regularityCost p + regularityCost s + t) / (1 + t) ≤ regularityCost (p + s) := by
  have hsum := regularityCost_sum_le hp hs
  have hm := one_le_regularityCost (show 2 ≤ p + s by omega)
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr ht)]

theorem regularityCost_le_twice {d : ℕ} (hd : 0 < d) :
    regularityCost d ≤ 2 * d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_le_sub_one_of_pos hd0
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  apply (div_le_iff₀ log_two_pos).mpr
  nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr hl2)]

/-- The factor 256 per dimension absorbs both half-density pruning losses. -/
theorem induction_constant_budget {p s : ℕ} (hp : 0 < p) (hs : 0 < s)
    {t : ℝ} (ht : 1 ≤ t) :
    8 * ((p + s : ℕ) : ℝ) + regularityCost p + regularityCost s +
      (((p + s : ℕ) : ℝ) + 3) * t ≤ 8 * ((p + s : ℕ) : ℝ) * (1 + t) := by
  have hpc := regularityCost_le_twice hp
  have hsc := regularityCost_le_twice hs
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ p + s - 2 by linarith) (sub_nonneg.mpr ht)]

end
end Erdos539Geometry
