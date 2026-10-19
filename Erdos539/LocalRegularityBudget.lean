/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerEstimates

namespace Erdos539Geometry

/-- The first conditional criterion from the remarks: if genuine local
regularity parameters satisfy the proposed product budget, a constant cost
closes the split. This does not assert those parameters exist. -/
theorem local_regularity_product_budget {R R₁ R₂ Rloc α t : ℝ}
    (hR : 1 ≤ R) (hR₁ : 1 ≤ R₁) (hR₂ : 1 ≤ R₂) (hloc : 1 ≤ Rloc)
    (hbudget : R₁ * R₂ * Rloc ≤ R ^ (2 : ℕ)) (hα : 2 ≤ α)
    (ht₁ : 1 ≤ t) (ht₂ : t ≤ 2) :
    R₁ ^ α * R₂ ^ α * Rloc ^ t ≤ R ^ (α * (1 + t)) := by
  have ha : 0 ≤ α := by linarith
  have hr : 0 ≤ R := by linarith
  have hr1 : 0 ≤ R₁ := by linarith
  have hr2 : 0 ≤ R₂ := by linarith
  have hrl : 0 ≤ Rloc := by linarith
  calc
    _ ≤ R₁ ^ α * R₂ ^ α * Rloc ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hloc (ht₂.trans hα)) (by positivity)
    _ = (R₁ * R₂ * Rloc) ^ α := by rw [Real.mul_rpow (mul_nonneg hr1 hr2) hrl, Real.mul_rpow hr1 hr2]
    _ ≤ (R ^ (2 : ℕ)) ^ α := Real.rpow_le_rpow (by positivity) hbudget ha
    _ = R ^ (2 * α) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
    _ ≤ R ^ (α * (1 + t)) := Real.rpow_le_rpow_of_exponent_le hR (by nlinarith)

end Erdos539Geometry
