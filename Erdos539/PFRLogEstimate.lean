/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.InductionEstimates

namespace Erdos539Geometry
noncomputable section

/-- Scalar estimate after weak PFR and the uniform regularity theorem.
`B`, `D`, and `Q` stand for the logarithms of the retained cardinality,
the original difference count, and the cofactor count, respectively. -/
theorem pfr_log_estimate {d : ℕ} (hd : 0 < d)
    {X T B D Q : ℝ} (hX : 0 ≤ X) (hT : 1 / 2 ≤ T)
    (hdT : (d : ℝ) ≤ 100 * T)
    (hB : X - 17 * T ≤ B) (hD : D ≤ X + T) (hQ : Q ≤ (X + T) / 2)
    (hregular : -8 * d * Real.log 2 + regularityCost d * (B - D) + uniformExponent d * B ≤ Q) :
    X ≤ 2000000 * T ^ 2 * (1 + Real.log (T + 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT0 : 0 ≤ T := by linarith
  have halpha := regularityCost_nonneg hd
  have hreg := mul_le_mul_of_nonneg_left (show -18 * T ≤ B - D by linarith) halpha
  have hvX := mul_le_mul_of_nonneg_right (uniformExponent_ge_half_add hd) hX
  have hvT := mul_le_mul_of_nonneg_right (uniformExponent_le_one hd) hT0
  have hvB := mul_le_mul_of_nonneg_left hB (uniformExponent_pos hd).le
  simp only [one_div] at hvX
  have hmain : X / (4 * d) ≤ 8 * d * Real.log 2 + (18 * regularityCost d + 18) * T := by
    rw [div_eq_mul_inv]
    nlinarith
  have hlog2low : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog2high : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  have halphalog : regularityCost d ≤ 2 * Real.log d := by
    apply (div_le_iff₀ log_two_pos).mpr
    nlinarith [mul_nonneg hlogd (sub_nonneg.mpr hlog2low)]
  have hTp1 : 0 < T + 1 := by linarith
  have hlogT : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have hdl := Real.log_le_log hd0 (show (d : ℝ) ≤ 100 * (T + 1) by linarith)
  rw [Real.log_mul (by norm_num : (100 : ℝ) ≠ 0) hTp1.ne'] at hdl
  have h100 : Real.log (100 : ℝ) ≤ 100 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100)
    linarith
  have hacost : regularityCost d ≤ 200 + 2 * Real.log (T + 1) := by linarith
  have hdlog : 8 * (d : ℝ) * Real.log 2 ≤ 800 * T := by
    have h := mul_le_mul_of_nonneg_left hlog2high hd0.le
    nlinarith
  have hcost : 8 * (d : ℝ) * Real.log 2 + (18 * regularityCost d + 18) * T ≤
      5000 * T * (1 + Real.log (T + 1)) := by
    have h := mul_le_mul_of_nonneg_right hacost hT0
    nlinarith [mul_nonneg hT0 hlogT]
  have hden : (0 : ℝ) < 4 * d := by positivity
  calc
    X ≤ (8 * (d : ℝ) * Real.log 2 + (18 * regularityCost d + 18) * T) * (4 * d) :=
      (div_le_iff₀ hden).mp hmain
    _ ≤ (5000 * T * (1 + Real.log (T + 1))) * (4 * d) :=
      mul_le_mul_of_nonneg_right hcost hden.le
    _ ≤ (5000 * T * (1 + Real.log (T + 1))) * (400 * T) := by
      apply mul_le_mul_of_nonneg_left (by linarith : (4 : ℝ) * d ≤ 400 * T)
      positivity
    _ = _ := by ring

theorem pfr_log_estimate_singleton {X T : ℝ} (hT : 1 / 2 ≤ T) (hX : X ≤ 17 * T) :
    X ≤ 2000000 * T ^ 2 * (1 + Real.log (T + 1)) := by
  have hT0 : 0 ≤ T := by linarith
  have hlogT : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have hsq : 17 * T ≤ 34 * T ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg T) hlogT]

end
end Erdos539Geometry
