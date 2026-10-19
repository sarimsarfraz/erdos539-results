/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ElementarySumsets
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

/-- An elementary telescoping upper bound for inverse square roots. -/
theorem inverse_sqrt_sum_le (n : ℕ) :
    ∑ x ∈ Finset.range n, 1 / Real.sqrt ((x : ℝ) + 1) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hp := Real.sqrt_pos.mpr hn1
    have hmono := Real.sqrt_le_sqrt (show (n : ℝ) ≤ n + 1 by linarith)
    have hsq := Real.sq_sqrt hn
    have hsq1 := Real.sq_sqrt hn1.le
    have hstep : 1 / Real.sqrt ((n : ℝ) + 1) ≤
        2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)]
    push_cast
    linarith

def scalarConvolutionWeight (n x : ℕ) : ℝ :=
  1 / Real.sqrt (((x : ℝ) + 1) * ((n - x : ℕ) + 1))

theorem scalarConvolutionWeight_nonneg (n x : ℕ) : 0 ≤ scalarConvolutionWeight n x := by
  unfold scalarConvolutionWeight
  positivity

theorem scalarConvolutionWeight_le (n x : ℕ) (hx : x ≤ n) :
    scalarConvolutionWeight n x ≤
      (1 / Real.sqrt ((x : ℝ) + 1) + 1 / Real.sqrt ((n - x : ℕ) + 1)) /
        Real.sqrt ((n : ℝ) + 1) := by
  have hj : (0 : ℝ) < x + 1 := by positivity
  have hk : (0 : ℝ) < (n - x : ℕ) + 1 := by positivity
  have hm : (0 : ℝ) < n + 1 := by positivity
  have hp := Real.sqrt_pos.mpr hj
  have hq := Real.sqrt_pos.mpr hk
  have hr := Real.sqrt_pos.mpr hm
  have hsum : (n : ℝ) + 1 ≤ ((x : ℝ) + 1) + ((n - x : ℕ) + 1) := by
    rw [Nat.cast_sub hx]
    linarith
  have hs : Real.sqrt ((n : ℝ) + 1) ≤
      Real.sqrt ((x : ℝ) + 1) + Real.sqrt ((n - x : ℕ) + 1) := by
    nlinarith [Real.sq_sqrt hj.le, Real.sq_sqrt hk.le, Real.sq_sqrt hm.le,
      mul_pos hp hq]
  unfold scalarConvolutionWeight
  rw [Real.sqrt_mul hj.le]
  apply (div_le_div_iff₀ (mul_pos hp hq) hr).mpr
  have he : (1 / Real.sqrt ((x : ℝ) + 1) + 1 / Real.sqrt ((n - x : ℕ) + 1)) *
      (Real.sqrt ((x : ℝ) + 1) * Real.sqrt ((n - x : ℕ) + 1)) =
      Real.sqrt ((x : ℝ) + 1) + Real.sqrt ((n - x : ℕ) + 1) := by
    field_simp
    ring
  simpa only [one_mul, he] using hs

/-- Scalar convolution is bounded uniformly, without an analytic integral. -/
theorem scalarConvolution_sum_le_four (n : ℕ) :
    ∑ x ∈ Finset.range (n + 1), scalarConvolutionWeight n x ≤ 4 := by
  have hp : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  calc
    _ ≤ ∑ x ∈ Finset.range (n + 1),
        (1 / Real.sqrt ((x : ℝ) + 1) + 1 / Real.sqrt ((n - x : ℕ) + 1)) /
          Real.sqrt ((n : ℝ) + 1) := by
      exact Finset.sum_le_sum (fun x hx ↦ scalarConvolutionWeight_le n x (by
        have := Finset.mem_range.mp hx; omega))
    _ = (2 * ∑ x ∈ Finset.range (n + 1), 1 / Real.sqrt ((x : ℝ) + 1)) /
        Real.sqrt ((n : ℝ) + 1) := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      have href := Finset.sum_range_reflect (fun x ↦ 1 / Real.sqrt ((x : ℝ) + 1)) (n + 1)
      simp only [Nat.add_sub_cancel, div_eq_mul_inv] at href
      rw [href]
      ring
    _ ≤ (2 * (2 * Real.sqrt ((n : ℝ) + 1))) / Real.sqrt ((n : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ hp.le
      have h := inverse_sqrt_sum_le (n + 1)
      push_cast at h
      linarith
    _ = 4 := by field_simp; norm_num

theorem scalarConvolution_sum_zero :
    ∑ x ∈ Finset.range (0 + 1), scalarConvolutionWeight 0 x = 1 := by
  simp [scalarConvolutionWeight]

end
end Erdos539Geometry
