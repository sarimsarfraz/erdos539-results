/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyVariation
import Erdos539.EnergyRestriction

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Actual hereditary norm retention for any exact optimizer. The subset
may be empty or have zero mass; no full-support hypothesis is assumed. -/
theorem energyNorm_hereditary {A S : Finset G} (hAS : A ⊆ S) (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    energyNorm S * weightSquareSum A (extendWeight S f) ^ 2 ≤ energyNorm A := by
  let h := restrictSupportWeight hAS f
  let g : S → ℝ := fun x ↦ extendWeight A h x
  let μ := weightSquareSum A (extendWeight S f)
  have hμ : 0 ≤ μ := weightSquareSum_nonneg A (extendWeight S f)
  have hNormPos : 0 < energyNorm S := energyNorm_pos hS
  have hinner : (∑ x : S, f x * g x) = μ := restrictSupportWeight_inner hAS f
  have hstat := energyMaximizer_stationary hf hE g
  rw [hinner] at hstat
  have hholder := mixedWeightedEnergy_fourth_le S (extendWeight S f) (extendWeight S f)
    (extendWeight S f) (extendWeight S g)
  rw [hstat, hE] at hholder
  have hext : extendWeight S g = extendWeight A h := extendWeight_lift hAS h
  have he : weightedEnergy S (extendWeight S g) = weightedEnergy A (extendWeight A h) := by
    rw [hext]
    exact restrictSupportWeight_energy hAS f
  rw [he] at hholder
  have hbound := energyNorm_bound A h
  have hnorm : (∑ x : A, h x ^ 2) = μ := restrictSupportWeight_squareSum hAS f
  rw [hnorm] at hbound
  have hretained : energyNorm S * μ ^ 4 ≤ weightedEnergy A (extendWeight A h) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hNormPos 3)).mp
    nlinarith
  by_cases hzero : μ = 0
  · change energyNorm S * μ ^ 2 ≤ energyNorm A
    rw [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact energyNorm_nonneg A
  · have hμp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ (pow_pos hμp 2)).mp
    change μ ^ 2 * (energyNorm S * μ ^ 2) ≤ μ ^ 2 * energyNorm A
    nlinarith

end
end Erdos539Geometry
