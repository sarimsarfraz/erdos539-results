/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.UniformGainInversion

namespace Erdos539
open Erdos539Geometry
noncomputable section

/-- A uniform geometric 1/d gain with bounded costs suffices for the stronger
unrestricted target. The geometric hypothesis remains explicit. -/
theorem cofactorThreshold_strong_bound_of_uniform_gain {U V c : ℝ}
    (hgain : UniformLogGainHypothesis U V c) (hU : 1 ≤ U) (hV : 0 ≤ V)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp (c' * Real.sqrt (Real.log n)) ≤ (cofactorThreshold n : ℝ) := by
  let C := uniformGainGrowthConstant U V c + 4
  have hC : 1 ≤ C := by
    dsimp only [C]
    linarith [uniformGainGrowthConstant_ge hU hV hc hc1]
  have hC0 : 0 < C := by linarith
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  let X₀ : ℝ := 16 * C + 1
  let N : ℕ := max 2 ⌈Real.exp X₀⌉₊
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnNat : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hceil : ⌈Real.exp X₀⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hexp : Real.exp X₀ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hlogn : X₀ ≤ Real.log n := (Real.le_log_iff_exp_le hnReal).mpr hexp
  have hX : 16 * C < Real.log n := by dsimp only [X₀] at hlogn; linarith
  obtain ⟨A, hA, hq⟩ := cofactorThreshold_attained n
  have h := hgain.cofactor_log_growth hU hV hc hc1 (show 2 ≤ A.card by omega)
  rw [hA, hq] at h
  exact lower_bound_from_quadratic_threshold_growth hnNat hC hX h.1 h.2

/-- End-to-end verification of the second sufficient criterion in the remarks.
This is an implication: it does not prove the joint projection hypothesis. -/
theorem cofactorThreshold_strong_bound_of_joint_projections {A B η : ℝ}
    (hproj : JointProjectionHypothesis A B η) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp (c * Real.sqrt (Real.log n)) ≤ (cofactorThreshold n : ℝ) := by
  exact cofactorThreshold_strong_bound_of_uniform_gain
    (hproj.uniformLogGain hA hB hη hη1) (by linarith) hB (by positivity) (by linarith)

end
end Erdos539
