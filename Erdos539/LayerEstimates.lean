/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos539Geometry

/-- The geometric mean constraint bounds the smaller side of an interior layer. -/
theorem layer_min_bound {x y a b Q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 < a) (hb : 0 < b) (hQ : 0 ≤ Q) (h : x ^ a * y ^ b ≤ Q) :
    min x y ≤ Q ^ (1 / (a + b)) := by
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (le_min hx hy) hQ (by linarith)).mpr
  rw [Real.rpow_add' (le_min hx hy) (by linarith : a + b ≠ 0)]
  apply (mul_le_mul (Real.rpow_le_rpow (le_min hx hy) (min_le_left _ _) ha.le)
    (Real.rpow_le_rpow (le_min hx hy) (min_le_right _ _) hb.le)
    (Real.rpow_nonneg (le_min hx hy) b) (Real.rpow_nonneg hx a)).trans h

/-- A layer's total size is bounded using the smaller exponent. -/
theorem layer_endpoint_bound {x y a b Q : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (ha : 0 < a) (hb : 0 < b) (hQ : 0 ≤ Q) (h : x ^ a * y ^ b ≤ Q) :
    x * y ≤ Q ^ (1 / min a b) := by
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) hQ (lt_min ha hb)).mpr
  rw [Real.mul_rpow (by linarith : 0 ≤ x) (by linarith : 0 ≤ y)]
  exact (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx (min_le_left _ _))
    (Real.rpow_le_rpow_of_exponent_le hy (min_le_right _ _))
    (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)).trans h

theorem layer_interior_bound {x y a b Q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 < a) (hb : 0 < b) (hQ : 0 ≤ Q) (h : x ^ a * y ^ b ≤ Q) :
    x * y ≤ Q ^ (1 / (a + b)) * (x + y) := by
  have hmin := layer_min_bound hx hy ha hb hQ h
  have hp := Real.rpow_nonneg hQ (1 / (a + b))
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy] at hmin
    nlinarith [mul_nonneg hp hx]
  · rw [min_eq_right hyx] at hmin
    nlinarith [mul_nonneg hp hy]

theorem layer_endpoint_log_closes {u m N M C L : ℝ}
    (hm : 0 < m) (hm1 : m ≤ 1) (hu : u ≤ m) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (h : N ≤ L + (M - C) / m) : C - L + u * N ≤ M := by
  have h' := (le_div_iff₀ hm).mp (show N - L ≤ (M - C) / m by linarith)
  have hu' := mul_le_mul_of_nonneg_right hu hN
  have hm' := mul_le_mul_of_nonneg_right hm1 hL
  nlinarith

theorem layer_interior_log_closes {u t N M C L : ℝ}
    (ht : 0 < t) (hu : u ≤ t / (1 + t)) (hN : 0 ≤ N) (hC : C ≤ 0) (hL : 0 ≤ L)
    (h : N ≤ L + M + (M - C) / t) : C - L + u * N ≤ M := by
  have h' := (le_div_iff₀ ht).mp (show N - L - M ≤ (M - C) / t by linarith)
  have hu' := (le_div_iff₀ (by linarith : 0 < 1 + t)).mp hu
  have huN := mul_le_mul_of_nonneg_right hu' hN
  have htC := mul_nonpos_of_nonneg_of_nonpos ht.le hC
  apply (mul_le_mul_iff_of_pos_right (by linarith : 0 < 1 + t)).mp
  nlinarith

/-- The two alternatives in the ordered-layer counting argument close with
only one extra factor four, independently of the number of layers. -/
theorem ordered_layer_scalar_bound {n q c a b u : ℝ}
    (hn : 1 ≤ n) (hq : 0 < q) (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1)
    (hua : u ≤ a) (hub : u ≤ b) (hu : u ≤ (a + b) / (1 + a + b))
    (hcount : n ≤ 2 * q * (q / c) ^ (1 / (a + b)) + 2 * (q / c) ^ (1 / min a b)) :
    c / 4 * n ^ u ≤ q := by
  have hnpos : 0 < n := by linarith
  have hQ : 0 < q / c := div_pos hq hc
  have hN : 0 ≤ Real.log n := Real.log_nonneg hn
  have hC : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hL : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hp := Real.rpow_pos_of_pos hnpos u
  have hc4 : 0 < c / 4 := div_pos hc (by norm_num)
  apply (Real.log_le_log_iff (mul_pos hc4 hp) hq).mp
  rw [Real.log_mul hc4.ne' hp.ne', Real.log_div hc.ne' (by norm_num : (4 : ℝ) ≠ 0), Real.log_rpow hnpos]
  by_cases he : n ≤ 4 * (q / c) ^ (1 / min a b)
  · have h := Real.log_le_log hnpos he
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hQ _).ne',
      Real.log_rpow hQ, Real.log_div hq.ne' hc.ne'] at h
    apply layer_endpoint_log_closes (lt_min ha hb) ((min_le_left _ _).trans ha1) (le_min hua hub) hN hL
    convert h using 1; ring
  · have hi : n ≤ 4 * q * (q / c) ^ (1 / (a + b)) := by linarith
    have h := Real.log_le_log hnpos hi
    rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 4) hq).ne' (Real.rpow_pos_of_pos hQ _).ne',
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hq.ne', Real.log_rpow hQ, Real.log_div hq.ne' hc.ne'] at h
    apply layer_interior_log_closes (by linarith : 0 < a + b) (by simpa only [add_assoc] using hu) hN hC hL
    convert h using 1; ring

end Erdos539Geometry
