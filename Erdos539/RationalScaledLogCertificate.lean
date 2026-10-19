/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RationalLogCertificate

namespace Erdos539Geometry

theorem rational_log_series_bounds {q : ℚ} (hq : 1 ≤ q) (n : ℕ) :
    (rationalLogSeries ((q - 1) / (q + 1)) n : ℝ) ≤ Real.log (q : ℝ) ∧
    Real.log (q : ℝ) ≤
      ((rationalLogSeries ((q - 1) / (q + 1)) n +
        2 * ((q - 1) / (q + 1)) ^ (2 * n + 1) /
          (1 - ((q - 1) / (q + 1)) ^ 2) : ℚ) : ℝ) := by
  have hp : 0 < q + 1 := by linarith
  have h0 : 0 ≤ (q - 1) / (q + 1) := div_nonneg (by linarith) hp.le
  have h1 : (q - 1) / (q + 1) < 1 := (div_lt_one hp).mpr (by linarith)
  have he : (1 + (((q - 1) / (q + 1) : ℚ) : ℝ)) /
      (1 - (((q - 1) / (q + 1) : ℚ) : ℝ)) = (q : ℝ) := by
    push_cast
    have hh : (q : ℝ) + 1 ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
    ring
  constructor
  · simpa only [he] using rationalLogSeries_lower h0 h1 n
  · simpa only [he] using rationalLogSeries_upper h0 h1 n

/-- A finite rational inequality certifies a real logarithm lower bound,
after extracting a power of two from its argument. -/
theorem rational_scaled_log_lower {q l : ℚ} (hq : 1 ≤ q) (k n : ℕ)
    (hc : l ≤ rationalLogSeries ((q - 1) / (q + 1)) n + k * (6931 / 10000)) :
    (l : ℝ) ≤ Real.log ((q : ℝ) * 2 ^ k) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by linarith)
  rw [Real.log_mul hq0 (pow_ne_zero _ (by norm_num)), Real.log_pow]
  have h := (rational_log_series_bounds hq n).1
  have ht := mul_le_mul_of_nonneg_left rational_log_two_bounds.1 (Nat.cast_nonneg k (α := ℝ))
  have hc' := (Rat.cast_le (K := ℝ)).mpr hc
  push_cast at hc'
  linarith

theorem rational_scaled_log_upper {q u : ℚ} (hq : 1 ≤ q) (k n : ℕ)
    (hc : rationalLogSeries ((q - 1) / (q + 1)) n +
      2 * ((q - 1) / (q + 1)) ^ (2 * n + 1) / (1 - ((q - 1) / (q + 1)) ^ 2) +
        k * (6932 / 10000) ≤ u) :
    Real.log ((q : ℝ) * 2 ^ k) ≤ (u : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by linarith)
  rw [Real.log_mul hq0 (pow_ne_zero _ (by norm_num)), Real.log_pow]
  have h := (rational_log_series_bounds hq n).2
  have ht := mul_le_mul_of_nonneg_left rational_log_two_bounds.2 (Nat.cast_nonneg k (α := ℝ))
  have hc' := Rat.cast_le (K := ℝ).mpr hc
  push_cast at hc' h
  linarith

end Erdos539Geometry
