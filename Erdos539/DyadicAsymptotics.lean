/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.DyadicRegularization

namespace Erdos539Geometry
noncomputable section
open Filter Topology

/-- The number of dyadic levels grows at most proportionally to log n. -/
theorem dyadicLevels_le_log {n : ℕ} (hn : 2 ≤ n) :
    (dyadicLevels n : ℝ) ≤ (2 / Real.log 2) * Real.log n := by
  have hn0 : n ≠ 0 := by omega
  have hpow := Nat.pow_log_le_self 2 hn0
  have hpow' : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast hpow
  have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow'
  rw [Real.log_pow] at hl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  apply (mul_le_mul_iff_right₀ hlog2).mp
  change Real.log 2 * (dyadicLevels n : ℝ) ≤ _
  have he : Real.log 2 * ((2 / Real.log 2) * Real.log n) = 2 * Real.log n := by field_simp [hlog2.ne']
  rw [he]
  unfold dyadicLevels
  push_cast
  nlinarith

/-- The regularization loss is negligible on the logarithmic exponent scale. -/
theorem tendsto_log_dyadicLevels_div_log :
    Tendsto (fun n : ℕ ↦ Real.log (dyadicLevels n) / Real.log n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ ↦ Real.log (2 / Real.log 2) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / Real.log n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hupper : Tendsto (fun n : ℕ ↦ Real.log (2 / Real.log 2) / Real.log n +
      Real.log (Real.log n) / Real.log n) atTop (𝓝 0) := by
    simpa only [add_zero] using hconst.add hloglog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlevels : (1 : ℝ) ≤ dyadicLevels n := by
      exact_mod_cast (show 1 ≤ dyadicLevels n by unfold dyadicLevels; omega)
    exact div_nonneg (Real.log_nonneg hlevels) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlevels : (0 : ℝ) < dyadicLevels n := by
      exact_mod_cast (show 0 < dyadicLevels n by unfold dyadicLevels; omega)
    have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hc : (0 : ℝ) < 2 / Real.log 2 := div_pos (by norm_num) (Real.log_pos (by norm_num))
    have h := Real.log_le_log hlevels (dyadicLevels_le_log hn)
    rw [Real.log_mul hc.ne' hnlog.ne'] at h
    simpa only [add_div] using div_le_div_of_nonneg_right h hnlog.le

end
end Erdos539Geometry
