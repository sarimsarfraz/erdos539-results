/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.QuadraticCoreGrowth
import Erdos539.QuadraticGrowthTransfer
import Erdos539.QuadraticThresholdInversion

namespace Erdos539Geometry
noncomputable section

theorem QuadraticCoreHypothesis.positive_log_growth {C : ℝ} (hcore : QuadraticCoreHypothesis C)
    (hC : 0 ≤ C) {A : Finset ℕ} (hA : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a) :
    Real.log A.card ≤ (10000 * C + 14470) * (growthParameter A.card (cofactors A).card) ^ 2 := by
  have hF : (integerExponentSet A).Nonempty := Finset.card_pos.mp (by
    rw [integerExponentSet_card hpos]
    exact hA.card_pos)
  simpa only [integerExponentSet_card hpos, integerPositiveDifferences_integerExponentSet_card hpos]
    using hcore.integer_log_growth hC hF

theorem QuadraticCoreHypothesis.cofactor_log_growth {C : ℝ} (hcore : QuadraticCoreHypothesis C)
    (hC : 0 ≤ C) {A : Finset ℕ} (hn : 2 ≤ A.card) :
    Real.log 2 ≤ thresholdGrowthParameter A.card (cofactors A).card ∧
      Real.log A.card ≤ (10000 * C + 14474) * (thresholdGrowthParameter A.card (cofactors A).card) ^ 2 := by
  simpa only [add_assoc, show (14470 : ℝ) + 4 = 14474 by norm_num] using
    cofactor_quadratic_growth_of_positive_bound (by linarith : 0 ≤ 10000 * C + 14470)
      (fun hA hpos ↦ hcore.positive_log_growth hC hA hpos) hn

end
end Erdos539Geometry

namespace Erdos539
open Erdos539Geometry
noncomputable section

/-- The paper's quadratic-core hypothesis suffices for the stronger lower
bound at the exact Formal Conjectures cofactorThreshold. The hypothesis is
explicit; this theorem does not assert that the quadratic bound is true. -/
theorem cofactorThreshold_strong_bound_of_quadratic_core {C₀ : ℝ}
    (hcore : QuadraticCoreHypothesis C₀) (hC₀ : 0 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp (c * Real.sqrt (Real.log n)) ≤ (cofactorThreshold n : ℝ) := by
  let C := 10000 * C₀ + 14474
  have hC : 1 ≤ C := by
    dsimp only [C]
    linarith
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
  have h := hcore.cofactor_log_growth hC₀ (show 2 ≤ A.card by omega)
  rw [hA, hq] at h
  exact lower_bound_from_quadratic_threshold_growth hnNat hC hX h.1 h.2

end
end Erdos539
