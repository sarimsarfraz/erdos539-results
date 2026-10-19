/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalPaletteInversion

namespace Erdos539Geometry
noncomputable section

/-- A purely rational certificate sufficient for the strict final
comparison. No floating-point logarithm estimate is used. -/
theorem log_four_ge_seven_sixths : (7 / 6 : ℝ) ≤ Real.log 4 := by
  have ha := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  have hb := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have htwo : Real.log (2 : ℝ) = Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  norm_num at ha hb
  linarith

/-- The numerical consequence of the codimension-one fractional-cover
inequality. That geometric entropy-cover input remains an explicit premise. -/
theorem log_norm_le_two_of_codimension_cover {d b L : ℝ}
    (hd : 3 ≤ d) (hb : 4 * d ≤ b) (hL : 0 ≤ L)
    (hcover : ((d - 2) / (2 * d) - 3 / (2 * b)) * L ≤ Real.log (1 + 1 / b)) :
    L ≤ 2 := by
  have hdpos : 0 < d := by linarith
  have hbpos : 0 < b := by linarith
  have hrecip := one_div_le_one_div_of_le (show 0 < 4 * d by positivity) hb
  have hs := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hbase : (1 : ℝ) / (8 * d) ≤ (4 * d - 11) / (8 * d) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have he : (d - 2) / (2 * d) - (3 / 2) * (1 / (4 * d)) = (4 * d - 11) / (8 * d) := by
    field_simp
    ring
  have he' : 3 / (2 * b) = (3 / 2 : ℝ) * (1 / b) := by ring
  have hcoef : 1 / (8 * d) ≤ (d - 2) / (2 * d) - 3 / (2 * b) := by
    rw [he']
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoef hL
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / b by positivity)
  have hsmall : (1 / (8 * d)) * L ≤ 1 / (4 * d) := by linarith
  have htwo : 1 / (4 * d) = (1 / (8 * d)) * 2 := by
    field_simp
    norm_num
  rw [htwo] at hsmall
  have hp : 0 < 1 / (8 * d) := by positivity
  nlinarith only [hsmall, hp]

/-- The elementary forbidden-cover contradiction, conditional on the
specified entropy-cover and full-dimension palette bounds. It does not
assert that those geometric inputs hold for a new class of cores. -/
theorem forbidden_codimension_cover_scalar {d b L q : ℝ}
    (hd : 3 ≤ d) (hb : 4 * d ≤ b) (hL : 0 ≤ L) (hq : d + 1 ≤ q)
    (hcritical : 2 * Real.log q ≤ (1 + 1 / b) * L)
    (hcover : ((d - 2) / (2 * d) - 3 / (2 * b)) * L ≤ Real.log (1 + 1 / b)) : False := by
  have hsmall := log_norm_le_two_of_codimension_cover hd hb hL hcover
  have hb12 : (12 : ℝ) ≤ b := by linarith
  have hrecip := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 12) hb12
  have hm := mul_le_mul_of_nonneg_right hrecip hL
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show 4 ≤ q by linarith)
  have hfour := log_four_ge_seven_sixths
  nlinarith

end
end Erdos539Geometry
