/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpSidonScalar

namespace Erdos539Geometry
noncomputable section

theorem sharpSidonExponent_strict_bounds : 2 < sharpSidonExponent ∧ sharpSidonExponent < 3 := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 := Real.log_lt_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) < 6)
  have h8 := Real.log_lt_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) < 8)
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
  · apply (lt_div_iff₀ hl).mpr
    linarith
  · apply (div_lt_iff₀ hl).mpr
    linarith

def sharpSeparatedExponent : ℝ := 1 / (sharpSidonExponent - 2)
def sharpRetentionBeta : ℝ := (sharpSidonExponent - 2) / (3 - sharpSidonExponent)
def sharpRetentionTau : ℝ := 1 / (3 - sharpSidonExponent)

theorem sharpSeparatedExponent_gt_one : 1 < sharpSeparatedExponent := by
  have hp := sharpSidonExponent_strict_bounds
  unfold sharpSeparatedExponent
  apply (lt_div_iff₀ (by linarith : 0 < sharpSidonExponent - 2)).mpr
  linarith

theorem sharpRetentionBeta_pos : 0 < sharpRetentionBeta :=
  div_pos (sub_pos.mpr sharpSidonExponent_strict_bounds.1)
    (sub_pos.mpr sharpSidonExponent_strict_bounds.2)

theorem sharpRetentionTau_eq_beta_add_one : sharpRetentionTau = sharpRetentionBeta + 1 := by
  have hp := sharpSidonExponent_strict_bounds
  have hd : 3 - sharpSidonExponent ≠ 0 := (sub_pos.mpr hp.2).ne'
  unfold sharpRetentionTau sharpRetentionBeta
  field_simp
  ring

theorem sharpRetentionBeta_mul_exponent_sub_one :
    sharpRetentionBeta * (sharpSeparatedExponent - 1) = 1 := by
  have hp := sharpSidonExponent_strict_bounds
  have h1 : sharpSidonExponent - 2 ≠ 0 := (sub_pos.mpr hp.1).ne'
  have h2 : 3 - sharpSidonExponent ≠ 0 := (sub_pos.mpr hp.2).ne'
  unfold sharpRetentionBeta sharpSeparatedExponent
  field_simp
  ring

/-- The exact logarithmic form of the sharp doubling-retention exponent. -/
theorem sharpRetentionTau_eq_log_ratio : sharpRetentionTau = Real.log 2 / Real.log (4 / 3 : ℝ) := by
  have h2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlog : Real.log (4 / 3 : ℝ) = 3 * Real.log 2 - Real.log 6 := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    have h6 := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
    have h4 := Real.log_pow (2 : ℝ) 2
    norm_num at h6 h4
    linarith
  rw [hlog]
  unfold sharpRetentionTau sharpSidonExponent
  field_simp

end
end Erdos539Geometry
