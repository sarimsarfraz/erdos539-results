/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProjectionCriterion
import Erdos539.PFRLogEstimate

namespace Erdos539Geometry
noncomputable section

def uniformGainGrowthConstant (U V c : ℝ) : ℝ := 100000 * (U + V + 1) / c

theorem uniformGainGrowthConstant_ge {U V c : ℝ} (hU : 1 ≤ U) (hV : 0 ≤ V)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) : 34 ≤ uniformGainGrowthConstant U V c := by
  apply (le_div_iff₀ hc).mpr
  nlinarith

theorem uniform_gain_pfr_scalar {d : ℕ} (hd : 0 < d) {U V c X T N Q Y : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (_hX : 0 ≤ X) (hT : 1 / 2 ≤ T) (hdT : (d : ℝ) ≤ 100 * T)
    (hN : X - 17 * T ≤ N) (hQ : Q ≤ (X + T) / 2) (hY : Y ≤ 18 * T)
    (hgain : (1 / 2 + c / d) * N - U * d - V * Y ≤ Q) :
    X ≤ uniformGainGrowthConstant U V c * T ^ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hv0 : 0 ≤ 1 / 2 + c / (d : ℝ) := by positivity
  have hv1 : 1 / 2 + c / (d : ℝ) ≤ 1 := by
    have hh : c / (d : ℝ) ≤ 1 / 2 := (div_le_iff₀ hd0).mpr (by nlinarith)
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hN hv0
  have hloss := mul_le_mul_of_nonneg_right hv1 (by linarith : 0 ≤ 17 * T)
  have hcost := mul_le_mul_of_nonneg_left hY hV
  have hmain : (c / (d : ℝ)) * X ≤ U * d + (18 * V + 18) * T := by nlinarith
  have hmain' := mul_le_mul_of_nonneg_right hmain hd0.le
  have hcancel : c / (d : ℝ) * X * d = c * X := by field_simp
  rw [hcancel] at hmain'
  have hU0 : 0 ≤ U := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hd2 : (d : ℝ) ^ 2 ≤ 10000 * T ^ 2 := by nlinarith
  have hterm1 := mul_le_mul_of_nonneg_left hd2 hU0
  have hterm2 := mul_le_mul_of_nonneg_right hdT
    (show 0 ≤ (18 * V + 18) * T by positivity)
  have hcoeff : 10000 * U + 1800 * V + 1800 ≤ 100000 * (U + V + 1) := by nlinarith
  have hcoeff' := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg T)
  have hfull : c * X ≤ 100000 * (U + V + 1) * T ^ 2 := by nlinarith
  have hC : uniformGainGrowthConstant U V c * c = 100000 * (U + V + 1) := div_mul_cancel₀ _ hc.ne'
  have hC' := congrArg (fun z : ℝ ↦ z * T ^ 2) hC
  apply (mul_le_mul_iff_of_pos_left hc).mp
  nlinarith

theorem uniform_gain_pfr_singleton {U V c X T : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (hT : 1 / 2 ≤ T) (hX : X ≤ 17 * T) :
    X ≤ uniformGainGrowthConstant U V c * T ^ 2 := by
  have hC := mul_le_mul_of_nonneg_right (uniformGainGrowthConstant_ge hU hV hc hc1) (sq_nonneg T)
  nlinarith

end
end Erdos539Geometry
