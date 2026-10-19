/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.AutocorrelationGeometry
import Erdos539.GibbsLogProducts

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

theorem two_correlation_loss_le_log {r c d : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hpair : r ^ 2 ≤ c * d) : 4 - 2 * c - 2 * d ≤ -4 * Real.log r := by
  have hs : (2 * r) ^ 2 ≤ (c + d) ^ 2 := by nlinarith [sq_nonneg (c - d)]
  have hlin : 2 * r ≤ c + d := (sq_le_sq₀ (by positivity) (add_nonneg hc hd)).mp hs
  linarith [Real.log_le_sub_one_of_pos hr]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def mixedEnergyGeometricMean (S : Finset G) (f g h k : G → ℝ) : ℝ :=
  weightedEnergy S f ^ (1 / 4 : ℝ) * weightedEnergy S g ^ (1 / 4 : ℝ) *
    weightedEnergy S h ^ (1 / 4 : ℝ) * weightedEnergy S k ^ (1 / 4 : ℝ)

theorem mixedEnergyGeometricMean_pos (S : Finset G) (f g h k : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g)
    (hh : 0 < weightedEnergy S h) (hk : 0 < weightedEnergy S k) : 0 < mixedEnergyGeometricMean S f g h k :=
  mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hf _) (Real.rpow_pos_of_pos hg _))
    (Real.rpow_pos_of_pos hh _)) (Real.rpow_pos_of_pos hk _)

theorem quarter_rpow_sq {a : ℝ} (ha : 0 ≤ a) : (a ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt a := by
  rw [← Real.rpow_mul_natCast ha, Real.sqrt_eq_rpow]
  norm_num

theorem mixedEnergyGeometricMean_sq (S : Finset G) (f g h k : G → ℝ) :
    mixedEnergyGeometricMean S f g h k ^ 2 =
      Real.sqrt (weightedEnergy S f) * Real.sqrt (weightedEnergy S g) *
        Real.sqrt (weightedEnergy S h) * Real.sqrt (weightedEnergy S k) := by
  simp only [mixedEnergyGeometricMean, mul_pow, quarter_rpow_sq (weightedEnergy_nonneg S _)]

theorem autocorrelationCosine_pair_normalization (S : Finset G) (f g h k : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g)
    (hh : 0 < weightedEnergy S h) (hk : 0 < weightedEnergy S k) :
    (autocorrelationCosine S f g * autocorrelationCosine S h k) * mixedEnergyGeometricMean S f g h k ^ 2 =
      autocorrelationInner S f g * autocorrelationInner S h k := by
  rw [autocorrelationCosine_eq, autocorrelationCosine_eq, mixedEnergyGeometricMean_sq]
  field_simp [(Real.sqrt_pos.mpr hf).ne', (Real.sqrt_pos.mpr hg).ne',
    (Real.sqrt_pos.mpr hh).ne', (Real.sqrt_pos.mpr hk).ne']

theorem mixed_ratio_pairing12 (S : Finset G) (f g h k : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g)
    (hh : 0 < weightedEnergy S h) (hk : 0 < weightedEnergy S k) :
    (mixedWeightedEnergy S f g h k / mixedEnergyGeometricMean S f g h k) ^ 2 ≤
      autocorrelationCosine S f g * autocorrelationCosine S h k := by
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos (mixedEnergyGeometricMean_pos S f g h k hf hg hh hk))).mpr
  rw [autocorrelationCosine_pair_normalization S f g h k hf hg hh hk]
  exact mixedEnergy_pairing12 S f g h k

theorem mixed_ratio_pairing13 (S : Finset G) (f g h k : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g)
    (hh : 0 < weightedEnergy S h) (hk : 0 < weightedEnergy S k) :
    (mixedWeightedEnergy S f g h k / mixedEnergyGeometricMean S f g h k) ^ 2 ≤
      autocorrelationCosine S f h * autocorrelationCosine S g k := by
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos (mixedEnergyGeometricMean_pos S f g h k hf hg hh hk))).mpr
  have he : mixedEnergyGeometricMean S f g h k = mixedEnergyGeometricMean S f h g k := by
    unfold mixedEnergyGeometricMean
    ring
  rw [he, autocorrelationCosine_pair_normalization S f h g k hf hh hg hk]
  exact mixedEnergy_pairing13 S f g h k

theorem mixed_ratio_pairing14 (S : Finset G) (f g h k : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g)
    (hh : 0 < weightedEnergy S h) (hk : 0 < weightedEnergy S k) :
    (mixedWeightedEnergy S f g h k / mixedEnergyGeometricMean S f g h k) ^ 2 ≤
      autocorrelationCosine S f k * autocorrelationCosine S h g := by
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos (mixedEnergyGeometricMean_pos S f g h k hf hg hh hk))).mpr
  have he : mixedEnergyGeometricMean S f g h k = mixedEnergyGeometricMean S f k h g := by
    unfold mixedEnergyGeometricMean
    ring
  rw [he, autocorrelationCosine_pair_normalization S f k h g hf hk hh hg]
  exact mixedEnergy_pairing14 S f g h k

/-- The six actual squared distances among normalized autocorrelations
are bounded by twelve times the mixed-energy Holder loss. -/
theorem six_autocorrelation_distances_le (S : Finset G) (f g h k : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g)
    (hh : 0 < weightedEnergy S h) (hk : 0 < weightedEnergy S k)
    (hK : 0 < mixedWeightedEnergy S f g h k) :
    autocorrelationDistanceSq S f g + autocorrelationDistanceSq S f h + autocorrelationDistanceSq S f k +
      autocorrelationDistanceSq S g h + autocorrelationDistanceSq S g k + autocorrelationDistanceSq S h k ≤
        12 * Real.log (mixedEnergyGeometricMean S f g h k / mixedWeightedEnergy S f g h k) := by
  have hH := mixedEnergyGeometricMean_pos S f g h k hf hg hh hk
  have hr := div_pos hK hH
  have h12 := two_correlation_loss_le_log hr (autocorrelationCosine_nonneg S f g)
    (autocorrelationCosine_nonneg S h k) (mixed_ratio_pairing12 S f g h k hf hg hh hk)
  have h13 := two_correlation_loss_le_log hr (autocorrelationCosine_nonneg S f h)
    (autocorrelationCosine_nonneg S g k) (mixed_ratio_pairing13 S f g h k hf hg hh hk)
  have h14 := two_correlation_loss_le_log hr (autocorrelationCosine_nonneg S f k)
    (autocorrelationCosine_nonneg S h g) (mixed_ratio_pairing14 S f g h k hf hg hh hk)
  have hc : autocorrelationCosine S h g = autocorrelationCosine S g h := by
    simp only [autocorrelationCosine, mul_comm]
  rw [hc] at h14
  rw [autocorrelationDistanceSq_eq S f g hf hg, autocorrelationDistanceSq_eq S f h hf hh,
    autocorrelationDistanceSq_eq S f k hf hk, autocorrelationDistanceSq_eq S g h hg hh,
    autocorrelationDistanceSq_eq S g k hg hk, autocorrelationDistanceSq_eq S h k hh hk,
    Real.log_div hH.ne' hK.ne']
  rw [Real.log_div hK.ne' hH.ne'] at h12 h13 h14
  linarith

end
end Erdos539Geometry
