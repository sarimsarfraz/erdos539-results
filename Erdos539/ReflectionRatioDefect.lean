/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedNormRetention

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem reflection_ratio_defect_lower {S : Finset G} (hS : S.Nonempty) {m : ℝ} (hm : 0 < m)
    (hR : ∀ w, energyNorm (reflectedSupport S w) ≤ energyNorm S * (24 / m ^ 2))
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    Real.log m - Real.log 24 / 2 ≤ finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S) := by
  let r := Real.sqrt 24 / m
  have hr : 0 ≤ r := div_nonneg (Real.sqrt_nonneg _) hm.le
  have hsq : r ^ 2 = 24 / m ^ 2 := by rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 24)]
  have hc := energyMaximizer_reflected_norm_cost hS hf hE hr (by simpa only [hsq] using hR)
  have hlog : Real.log r = Real.log 24 / 2 - Real.log m := by
    rw [Real.log_div (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 24)).ne' hm.ne',
      Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 24)]
  rw [hlog] at hc
  linarith

theorem endpoint_defect_le_of_card_norm {S : Finset G} (hS : S.Nonempty) {a : ℝ} (ha : 0 < a)
    (hN : (S.card : ℝ) ≤ a * energyNorm S) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    finiteEntropy ν - Real.log (energyNorm S) ≤ Real.log a := by
  letI : Nonempty S := hS.coe_sort
  have hH := finiteEntropy_le_log_card ν hν hs
  simp only [Fintype.card_coe] at hH
  have hlog := Real.log_le_log (by exact_mod_cast hS.card_pos : (0 : ℝ) < S.card) hN
  rw [Real.log_mul ha.ne' (energyNorm_pos hS).ne'] at hlog
  linarith

theorem reflection_loss_of_norm_bound {S : Finset G} (hS : S.Nonempty) {m : ℝ} (hm : 0 < m)
    (w : G) (hw : (reflectedSupport S w).Nonempty)
    (hr : energyNorm (reflectedSupport S w) ≤ energyNorm S * (24 / m ^ 2)) :
    2 * Real.log m - Real.log 24 ≤ Real.log (energyNorm S / energyNorm (reflectedSupport S w)) := by
  have hlog := Real.log_le_log (energyNorm_pos hw) hr
  rw [Real.log_mul (energyNorm_pos hS).ne' (div_pos (by norm_num) (pow_pos hm 2)).ne',
    Real.log_div (by norm_num : (24 : ℝ) ≠ 0) (pow_pos hm 2).ne', Real.log_pow] at hlog
  rw [Real.log_div (energyNorm_pos hS).ne' (energyNorm_pos hw).ne']
  norm_num at hlog
  linarith

end
end Erdos539Geometry
