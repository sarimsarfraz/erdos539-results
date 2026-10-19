/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos539Geometry
open scoped BigOperators

/-- Rational partial sum for log((1+x)/(1-x)); the accompanying bounds
are real inequalities, not floating-point evaluation. -/
def rationalLogSeries (x : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)

theorem rationalLogSeries_lower {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (rationalLogSeries x n : ℝ) ≤ Real.log ((1 + (x : ℝ)) / (1 - x)) := by
  have h := Real.sum_range_le_log_div (x := (x : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1) n
  push_cast [rationalLogSeries]
  linarith

theorem rationalLogSeries_upper {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    Real.log ((1 + (x : ℝ)) / (1 - x)) ≤
      ((rationalLogSeries x n + 2 * x ^ (2 * n + 1) / (1 - x ^ 2) : ℚ) : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (x : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1) n
  push_cast [rationalLogSeries]
  rw [mul_div_assoc]
  linarith

theorem rational_log_two_bounds : (6931 / 10000 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (6932 / 10000 : ℝ) := by
  have hL := rationalLogSeries_lower (x := 1 / 3) (by norm_num) (by norm_num) 5
  have hU := rationalLogSeries_upper (x := 1 / 3) (by norm_num) (by norm_num) 5
  norm_num [rationalLogSeries, Finset.sum_range_succ] at hL hU
  constructor <;> linarith

end Erdos539Geometry
