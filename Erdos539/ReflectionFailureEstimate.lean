/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RationalLogCertificate

namespace Erdos539Geometry

/-- The numerical union-bound estimate holds for every real m>=10, hence
for every integer parameter in the sparse reflection construction. -/
theorem reflection_failure_estimate {m : ℝ} (hm : 10 ≤ m) :
    2 * Real.exp (-(m ^ 11) / 12) + 4 * m ^ 24 * Real.exp (-(m ^ 8) / 48) < 1 := by
  have hmp : 0 < m := by linarith
  have hlogm : Real.log m ≤ m := by linarith [Real.log_le_sub_one_of_pos hmp]
  have hlog2 : Real.log 2 < 1 := by linarith [rational_log_two_bounds.2]
  have h7 : (10 : ℝ) ^ 7 ≤ m ^ 7 := pow_le_pow_left₀ (by norm_num) hm 7
  have h8 : (10 : ℝ) ^ 7 * m ≤ m ^ 8 := by nlinarith [mul_le_mul_of_nonneg_right h7 hmp.le]
  have h11 : (10 : ℝ) ^ 11 ≤ m ^ 11 := pow_le_pow_left₀ (by norm_num) hm 11
  have hquarter : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hfirst : 2 * Real.exp (-(m ^ 11) / 12) < 1 / 4 := by
    rw [← hquarter]
    calc
      _ = Real.exp (Real.log 2 - m ^ 11 / 12) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        congr 2
        ring
      _ < _ := Real.exp_lt_exp.mpr (by norm_num at h11; nlinarith)
  have hsecond : 4 * m ^ 24 * Real.exp (-(m ^ 8) / 48) < 1 / 4 := by
    rw [← hquarter]
    calc
      _ = Real.exp (2 * Real.log 2 + (24 : ℕ) * Real.log m - m ^ 8 / 48) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
          show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
          Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          Real.exp_nat_mul, Real.exp_log hmp]
        rw [show -(m ^ 8) / 48 = -(m ^ 8 / 48) by ring]
        norm_num
      _ < _ := Real.exp_lt_exp.mpr (by norm_num at h8 ⊢; nlinarith)
  linarith

end Erdos539Geometry
