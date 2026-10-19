/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpExponents
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos539Geometry

/-- The manuscript's logarithmic-loss exponent, equal to `2^(d+1)-4`. -/
def sharpLogLoss (d : ℕ) : ℝ := 2 * ((2 : ℝ) ^ d - 2)

theorem sharpLogLoss_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    sharpLogLoss p + sharpLogLoss s ≤ sharpLogLoss (p + s) := by
  have hP : (2 : ℝ) ≤ 2 ^ p := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
  have hS : (2 : ℝ) ≤ 2 ^ s := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
  unfold sharpLogLoss
  rw [pow_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hS)]

/-- Scalar closure of the regularized sharp-exponent induction. -/
theorem sharp_lower_split_closes {d a b u r q N E P Q M L K : ℝ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hq : q ≤ 2 * r)
    (hu : u ≤ (a + b) / (1 + a + b))
    (hsize : N ≤ r * K + E)
    (hP : P ≤ (d + 3) * L + r * K + M)
    (hQ : Q ≤ (d + 3) * L + r * K + M)
    (hprune : a * (E - L - Q) + b * (E - L - P) - 8 * d * L - q * K ≤ M) :
    u * N - 8 * d * L - 2 * r * K ≤ M := by
  have hden : 0 < 1 + a + b := by linarith
  have hu' := (le_div_iff₀ hden).mp hu
  have hNu := mul_le_mul_of_nonneg_right hu' hN
  have hPa := mul_le_mul_of_nonneg_left hQ ha
  have hPb := mul_le_mul_of_nonneg_left hP hb
  have hsize' := mul_le_mul_of_nonneg_left hsize (show 0 ≤ a + b by linarith)
  have hconstant : (d + 4) * (a + b) ≤ 8 * d * (a + b) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hconstant' := mul_le_mul_of_nonneg_right hconstant hL
  have hq' := mul_le_mul_of_nonneg_right hq hK
  apply (mul_le_mul_iff_right₀ hden).mp
  nlinarith

/-- An empty part of the balanced split already gives the desired bound. -/
theorem sharp_lower_empty_closes {d u r N E M L K : ℝ}
    (hd : 1 ≤ d) (hu : u ≤ 1) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hsize : N ≤ r * K + E) (hproj : E ≤ (d + 3) * L + r * K + M) :
    u * N - 8 * d * L - 2 * r * K ≤ M := by
  have huN := mul_le_mul_of_nonneg_right hu hN
  have hconstant := mul_le_mul_of_nonneg_right (show d + 3 ≤ 8 * d by linarith) hL
  nlinarith

end Erdos539Geometry
