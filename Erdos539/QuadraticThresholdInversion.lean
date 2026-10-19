/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CofactorGrowth

namespace Erdos539Geometry
noncomputable section

/-- Quadratic logarithmic growth has a square-root-logarithmic inverse. -/
theorem uniform_growth_inversion {C X T : ℝ} (hC : 1 ≤ C) (hX : 16 * C < X)
    (hT : 0 ≤ T) (hbound : X ≤ C * T ^ 2) : 4 < T ∧ Real.sqrt X ≤ C * T := by
  have hC0 : 0 ≤ C := by linarith
  have hlarge : 4 < T := by
    by_contra hh
    have hT4 : T ≤ 4 := le_of_not_gt hh
    have hsq : T ^ 2 ≤ 16 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq hC0
    nlinarith
  refine ⟨hlarge, Real.sqrt_le_iff.mpr ⟨mul_nonneg hC0 hT, ?_⟩⟩
  have h := mul_nonneg (mul_nonneg hC0 (sub_nonneg.mpr hC)) (sq_nonneg T)
  nlinarith

/-- The exact zero-inclusive cofactor threshold convention only costs a
constant in this conditional stronger inversion. -/
theorem lower_bound_from_quadratic_threshold_growth {n q : ℕ} (hn : 0 < n)
    {C : ℝ} (hC : 1 ≤ C) (hX : 16 * C < Real.log n)
    (hTlower : Real.log 2 ≤ thresholdGrowthParameter n q)
    (hbound : Real.log n ≤ C * (thresholdGrowthParameter n q) ^ 2) :
    Real.sqrt n * Real.exp ((1 / (4 * C)) * Real.sqrt (Real.log n)) ≤ q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hC0 : 0 < C := by linarith
  let T := thresholdGrowthParameter n q
  have hqNat : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    simp only [hq0, thresholdGrowthParameter, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, mul_zero, Real.log_zero] at hTlower
    linarith [log_two_pos]
  have hq : (0 : ℝ) < q := by exact_mod_cast hqNat
  obtain ⟨hT4, hsqrt⟩ := uniform_growth_inversion hC hX (log_two_pos.le.trans hTlower) hbound
  have hTdef : T = Real.log 4 + 2 * Real.log q - Real.log n := by
    dsimp only [T, thresholdGrowthParameter]
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (div_pos (sq_pos_of_pos hq) hn').ne',
      Real.log_div (sq_pos_of_pos hq).ne' hn'.ne', Real.log_pow]
    norm_num
    ring
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have hpow := Real.log_pow (2 : ℝ) 2
    norm_num at hpow
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hgain : (1 / (4 * C)) * Real.sqrt (Real.log n) ≤ T / 4 := by
    calc
      _ = Real.sqrt (Real.log n) / (4 * C) := by ring
      _ ≤ (C * T) / (4 * C) := div_le_div_of_nonneg_right hsqrt (by positivity)
      _ = T / 4 := by field_simp
  have hlogq : Real.log n / 2 + (1 / (4 * C)) * Real.sqrt (Real.log n) ≤ Real.log q := by
    change 4 < T at hT4
    linarith
  apply (Real.log_le_log_iff (mul_pos (Real.sqrt_pos.mpr hn') (Real.exp_pos _)) hq).mp
  rw [Real.log_mul (Real.sqrt_pos.mpr hn').ne' (Real.exp_pos _).ne', Real.log_sqrt hn'.le,
    Real.log_exp]
  exact hlogq

end
end Erdos539Geometry
