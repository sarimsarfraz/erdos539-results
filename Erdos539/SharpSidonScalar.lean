/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SidonRatio
import Mathlib.Tactic.FieldSimp

namespace Erdos539Geometry
noncomputable section

/-- The sharp two-point additive-energy exponent of Kane--Tao,
A bound on partitioning clusters, Lemma 8 and Remark 9 (arXiv:1702.00912v2).
The local proof uses a concavity/sign argument without numerical roots. -/
def sharpSidonExponent : ℝ := Real.log 6 / Real.log 2

theorem sharpSidonExponent_bounds : 2 ≤ sharpSidonExponent ∧ sharpSidonExponent ≤ 3 := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 6)
  have h8 := Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 8)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have height : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  unfold sharpSidonExponent
  constructor
  · apply (le_div_iff₀ hl).mpr
    linarith
  · apply (div_le_iff₀ hl).mpr
    linarith

theorem two_rpow_sharpSidonExponent : (2 : ℝ) ^ sharpSidonExponent = 6 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have he : Real.log 2 * sharpSidonExponent = Real.log 6 := by
    unfold sharpSidonExponent
    field_simp
  rw [he, Real.exp_log (by norm_num : (0 : ℝ) < 6)]

/-- Scaling the normalized inequality, with a zero smaller weight
allowed. -/
theorem sidon_scalar_of_le {p a b : ℝ} (hp2 : 2 ≤ p) (hp3 : p ≤ 3)
    (hend : (6 : ℝ) ≤ 2 ^ p) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    a ^ p + 4 * (a * b) ^ (p / 2) + b ^ p ≤ (a + b) ^ p := by
  have hx : a / b ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ha hb.le, (div_le_one hb).mpr hab⟩
  have h := mul_le_mul_of_nonneg_right (sidon_scalar_unit hp2 hp3 hend hx) (Real.rpow_nonneg hb.le p)
  have hbp : b ^ p ≠ 0 := (Real.rpow_pos_of_pos hb p).ne'
  have hbh : b ^ (p / 2) ≠ 0 := (Real.rpow_pos_of_pos hb (p / 2)).ne'
  have hpow : b ^ p = b ^ (p / 2) * b ^ (p / 2) := by
    rw [← Real.rpow_add hb]
    congr 1
    ring
  have he1 : (a / b) ^ p * b ^ p = a ^ p := by
    rw [Real.div_rpow ha hb.le]
    exact div_mul_cancel₀ _ hbp
  have he2 : (a / b) ^ (p / 2) * b ^ p = (a * b) ^ (p / 2) := by
    rw [Real.div_rpow ha hb.le, hpow, Real.mul_rpow ha hb.le]
    field_simp
  have he3 : (1 + a / b) ^ p * b ^ p = (a + b) ^ p := by
    rw [← Real.mul_rpow (by linarith [hx.1] : 0 ≤ 1 + a / b) hb.le]
    congr 1
    field_simp
    ring
  simp only [add_mul, mul_assoc, one_mul, he1, he2, he3] at h
  exact h

/-- The exact sharp two-variable Sidon inequality, including both zero
weights. The logarithmic exponent is proved rather than assumed. -/
theorem sharp_sidon_scalar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ sharpSidonExponent + 4 * (a * b) ^ (sharpSidonExponent / 2) + b ^ sharpSidonExponent ≤
      (a + b) ^ sharpSidonExponent := by
  have hp := sharpSidonExponent_bounds
  have hend : (6 : ℝ) ≤ 2 ^ sharpSidonExponent := two_rpow_sharpSidonExponent.ge
  by_cases hab : a ≤ b
  · by_cases hb0 : b = 0
    · have ha0 : a = 0 := by linarith
      have hpos : 0 < sharpSidonExponent := by linarith [hp.1]
      simp [ha0, hb0, Real.zero_rpow hpos.ne', Real.zero_rpow (show sharpSidonExponent / 2 ≠ 0 by positivity)]
    · exact sidon_scalar_of_le hp.1 hp.2 hend ha (lt_of_le_of_ne hb (Ne.symm hb0)) hab
  · have ha0 : 0 < a := lt_of_le_of_lt hb (lt_of_not_ge hab)
    have h := sidon_scalar_of_le hp.1 hp.2 hend hb ha0 (le_of_not_ge hab)
    simpa only [mul_comm b a, add_comm b a, add_comm, add_left_comm, add_assoc] using h

end
end Erdos539Geometry
