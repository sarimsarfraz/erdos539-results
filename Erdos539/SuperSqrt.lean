/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GrowthInversion

namespace Erdos539
open Erdos539Geometry
noncomputable section

theorem cofactorThreshold_log_growth {n : ℕ} (hn : 2 ≤ n) :
    Real.log 2 ≤ thresholdGrowthParameter n (cofactorThreshold n) ∧
    Real.log n ≤ 4000000 * (thresholdGrowthParameter n (cofactorThreshold n)) ^ 2 *
      (1 + Real.log (thresholdGrowthParameter n (cofactorThreshold n) + 1)) := by
  obtain ⟨A, hA, hq⟩ := cofactorThreshold_attained n
  have h := cofactor_log_growth (show 2 ≤ A.card by omega)
  simpa only [hA, hq] using h

/-- Priority 1, with the explicit positive constant `1/16000`, for the exact
zero-inclusive `cofactorThreshold` definition from Formal Conjectures.
The proof uses elementary original-coordinate extraction, without weak PFR. -/
theorem cofactorThreshold_super_sqrt_explicit :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp ((1 / 16000 : ℝ) * Real.sqrt (Real.log n / Real.log (Real.log n)))
        ≤ (cofactorThreshold n : ℝ) := by
  let X₀ : ℝ := max 320000001 (Real.exp 1)
  let N : ℕ := max 2 ⌈Real.exp X₀⌉₊
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnNat : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hceil : ⌈Real.exp X₀⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hexp : Real.exp X₀ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hlogn : X₀ ≤ Real.log n := (Real.le_log_iff_exp_le hnReal).mpr hexp
  have hX : 320000000 < Real.log n := by
    have h := (le_max_left 320000001 (Real.exp 1)).trans hlogn
    linarith
  have hlogX : 1 ≤ Real.log (Real.log n) := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right 320000001 (Real.exp 1)).trans hlogn)
    simpa only [Real.log_exp] using h
  obtain ⟨hT, hgrowth⟩ := cofactorThreshold_log_growth hn2
  exact lower_bound_from_threshold_growth hnNat hX hlogX hT hgrowth

/-- The requested existential-constant statement. -/
theorem cofactorThreshold_super_sqrt :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp (c * Real.sqrt (Real.log n / Real.log (Real.log n)))
        ≤ (cofactorThreshold n : ℝ) :=
  ⟨1 / 16000, by norm_num, cofactorThreshold_super_sqrt_explicit⟩

end
end Erdos539

#print axioms Erdos539.cofactorThreshold_super_sqrt
