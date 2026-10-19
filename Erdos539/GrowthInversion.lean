/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CofactorGrowth

namespace Erdos539Geometry
noncomputable section

/-- Elementary inversion with explicit numerical constants. -/
theorem growth_inversion {X T : ℝ} (hX : 320000000 < X) (hlogX : 1 ≤ Real.log X)
    (hT : 1 / 2 ≤ T)
    (hbound : X ≤ 4000000 * T ^ 2 * (1 + Real.log (T + 1))) :
    4 < T ∧ Real.sqrt (X / Real.log X) ≤ 4000 * T := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTp1 : 0 < T + 1 := by linarith
  have hlogXp : 0 < Real.log X := by linarith
  have hlogTp : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have hlarge : 4 < T := by
    by_contra hh
    have hT4 : T ≤ 4 := le_of_not_gt hh
    have hlog := Real.log_le_log hTp1 (show T + 1 ≤ 5 by linarith)
    have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    have hlog4 : Real.log (T + 1) ≤ 4 := by linarith
    have hsq : T ^ 2 ≤ 16 := by nlinarith
    have hb : 4000000 * T ^ 2 * (1 + Real.log (T + 1)) ≤ 320000000 := by
      calc
        _ ≤ 4000000 * T ^ 2 * 5 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ 4000000 * 16 * 5 := by nlinarith
        _ = _ := by norm_num
    linarith
  refine ⟨hlarge, Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩⟩
  by_cases hTX : X ≤ T
  · have hratio : X / Real.log X ≤ X := by
      apply (div_le_iff₀ hlogXp).mpr
      nlinarith [mul_nonneg hX0.le (sub_nonneg.mpr hlogX)]
    nlinarith [sq_nonneg (T - 1)]
  · have hTX' : T < X := lt_of_not_ge hTX
    have hlog := Real.log_le_log hTp1 (show T + 1 ≤ 2 * X by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at hlog
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hf : 1 + Real.log (T + 1) ≤ 3 * Real.log X := by linarith
    have hx : X ≤ 12000000 * T ^ 2 * Real.log X := by
      have h := mul_le_mul_of_nonneg_left hf (show 0 ≤ 4000000 * T ^ 2 by positivity)
      nlinarith
    apply (div_le_iff₀ hlogXp).mpr
    nlinarith [mul_nonneg (sq_nonneg T) hlogXp.le]

theorem lower_bound_from_threshold_growth {n q : ℕ} (hn : 0 < n)
    (hX : 320000000 < Real.log n) (hlogX : 1 ≤ Real.log (Real.log n))
    (hTlower : Real.log 2 ≤ thresholdGrowthParameter n q)
    (hbound : Real.log n ≤ 4000000 * (thresholdGrowthParameter n q) ^ 2 *
      (1 + Real.log (thresholdGrowthParameter n q + 1))) :
    Real.sqrt n * Real.exp ((1 / 16000 : ℝ) * Real.sqrt (Real.log n / Real.log (Real.log n))) ≤ q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let T := thresholdGrowthParameter n q
  have h2low : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hqNat : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    simp only [hq0, thresholdGrowthParameter, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, mul_zero, Real.log_zero] at hTlower
    linarith [log_two_pos]
  have hq : (0 : ℝ) < q := by exact_mod_cast hqNat
  obtain ⟨hT4, hsqrt⟩ := growth_inversion hX hlogX (h2low.trans hTlower) hbound
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
  have hlogq : Real.log n / 2 +
      (1 / 16000 : ℝ) * Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ Real.log q := by
    change 4 < T at hT4
    change Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ 4000 * T at hsqrt
    linarith
  apply (Real.log_le_log_iff (mul_pos (Real.sqrt_pos.mpr hn') (Real.exp_pos _)) hq).mp
  rw [Real.log_mul (Real.sqrt_pos.mpr hn').ne' (Real.exp_pos _).ne', Real.log_sqrt hn'.le,
    Real.log_exp]
  exact hlogq

end
end Erdos539Geometry
