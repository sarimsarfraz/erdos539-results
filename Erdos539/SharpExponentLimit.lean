/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpLowerBounds
import Erdos539.DyadicAsymptotics

namespace Erdos539Geometry
noncomputable section
open Filter Topology

/-- In every fixed positive dimension, the logarithmic exponent of the actual
integer-vector minimum is exactly the minimizing-split exponent. -/
theorem fixedDimensionalMinimum_log_exponent {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ Real.log (fixedDimensionalMinimum d n) / Real.log n)
      atTop (𝓝 (sharpExponent d : ℝ)) := by
  obtain ⟨C, hC, hupper⟩ := fixedDimensionalMinimum_sharp_upper hd
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : ℕ ↦ (8 * (d : ℝ) * Real.log 2) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hdyadic : Tendsto (fun n : ℕ ↦ sharpLogLoss d * (Real.log (dyadicLevels n) / Real.log n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_log_dyadicLevels_div_log.const_mul (sharpLogLoss d)
  have hlo : Tendsto (fun n : ℕ ↦ (sharpExponent d : ℝ) - (8 * (d : ℝ) * Real.log 2) / Real.log n -
      sharpLogLoss d * (Real.log (dyadicLevels n) / Real.log n)) atTop (𝓝 (sharpExponent d : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hconstant).sub hdyadic
  have hCdiv : Tendsto (fun n : ℕ ↦ Real.log C / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hhi : Tendsto (fun n : ℕ ↦ (sharpExponent d : ℝ) + Real.log C / Real.log n)
      atTop (𝓝 (sharpExponent d : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hCdiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : 0 < n := by omega
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have h := fixedDimensionalMinimum_sharp_log_lower hd hn0
    apply (le_div_iff₀ hln).mpr
    calc
      _ = (sharpExponent d : ℝ) * Real.log n - 8 * (d : ℝ) * Real.log 2 -
          sharpLogLoss d * Real.log (dyadicLevels n) := by field_simp [hln.ne']
      _ ≤ _ := h
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : 0 < n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hq : (0 : ℝ) < fixedDimensionalMinimum d n := by exact_mod_cast fixedDimensionalMinimum_pos hd hn0
    have hp : 0 < (n : ℝ) ^ (sharpExponent d : ℝ) := Real.rpow_pos_of_pos hnpos _
    have h := Real.log_le_log hq (hupper n hn0)
    rw [Real.log_mul hC.ne' hp.ne', Real.log_rpow hnpos] at h
    apply (div_le_iff₀ hln).mpr
    calc
      _ ≤ Real.log C + (sharpExponent d : ℝ) * Real.log n := h
      _ = _ := by field_simp [hln.ne']; ring

/-- The same exact limiting exponent for integers supported on any chosen
list of distinct primes; the arithmetic dictionary has no loss. -/
theorem primeSupportedMinimum_log_exponent {d : ℕ} (hd : 0 < d)
    (p : Fin d ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    Tendsto (fun n : ℕ ↦ Real.log (primeSupportedMinimum p n) / Real.log n)
      atTop (𝓝 (sharpExponent d : ℝ)) := by
  simpa only [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp] using
    fixedDimensionalMinimum_log_exponent hd

end
end Erdos539Geometry
