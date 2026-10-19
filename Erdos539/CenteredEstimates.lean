/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerEstimates

namespace Erdos539Geometry

/-- The rank-weighted losses of the two children fit the parent's loss. -/
theorem centered_rank_budget {a b r rI rJ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hI : 0 ≤ rI) (hJ : 0 ≤ rJ)
    (hr : rI + rJ ≤ r) :
    (1 + a) * rI + (1 + b) * rJ ≤ (1 + a + b) * r := by
  have h := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 1 + a + b)
  nlinarith [mul_nonneg ha hJ, mul_nonneg hb hI]

/-- The exact sharp recursion closes the centered midpoint induction with
constant 2^(-d-2r). All variables here are logarithms or ranks. -/
theorem centered_log_closes {a b u N Q A B QA QB d p s r rI rJ L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hI : 0 ≤ rI) (hJ : 0 ≤ rJ) (hr : rI + rJ ≤ r) (hd : p + s = d)
    (hu : u ≤ (a + b) / (1 + a + b))
    (hA : N ≤ d * L + Q + 2 * rI * L + A)
    (hB : N ≤ d * L + Q + 2 * rJ * L + B)
    (hQA : a * A - (p + 2 * rI) * L ≤ QA)
    (hQB : b * B - (s + 2 * rJ) * L ≤ QB)
    (hprod : QA + QB ≤ Q) :
    u * N - (d + 2 * r) * L ≤ Q := by
  have hAa := mul_le_mul_of_nonneg_left hA ha
  have hBb := mul_le_mul_of_nonneg_left hB hb
  have hrL := mul_le_mul_of_nonneg_right (centered_rank_budget ha hb hI hJ hr) hL
  have hrec := (le_div_iff₀ (by linarith : 0 < 1 + a + b)).mp hu
  have hrecN := mul_le_mul_of_nonneg_right hrec hN
  apply (mul_le_mul_iff_of_pos_right (by linarith : 0 < 1 + a + b)).mp
  nlinarith

/-- An empty side leaves a faithful full projection, which is enough since u≤1. -/
theorem centered_empty_log_closes {u N Q d r L : ℝ}
    (hu : u ≤ 1) (hN : 0 ≤ N) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (h : N ≤ d * L + Q) : u * N - (d + 2 * r) * L ≤ Q := by
  have hh := mul_le_mul_of_nonneg_right hu hN
  nlinarith [mul_nonneg hr hL]

end Erdos539Geometry
