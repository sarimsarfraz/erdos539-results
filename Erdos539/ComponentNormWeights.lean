/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SeparatedComponentEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]

omit [Fintype ι] in
theorem componentWeight_energy_bound (S : Finset G) (label : G → ι) (w : G → ℝ) (i : ι) :
    weightedEnergy S (componentWeight label w i) ≤
      energyNorm (fiber S label i) * weightSquareSum S (componentWeight label w i) ^ 2 := by
  apply weightedEnergy_le_support_norm (show fiber S label i ⊆ S from Finset.filter_subset _ _)
  intro x hx hnot
  have hne : label x ≠ i := fun h ↦ hnot (mem_fiber.mpr ⟨hx, h⟩)
  simp [componentWeight, hne]

omit [AddCommGroup G] [DecidableEq G] in
theorem componentWeight_squareSum_total (S : Finset G) (label : G → ι) (w : G → ℝ) :
    (∑ i, weightSquareSum S (componentWeight label w i)) = weightSquareSum S w := by
  unfold weightSquareSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [componentWeight]

omit [Fintype ι] in
theorem component_fourth_power (S : Finset G) (label : G → ι) (w : G → ℝ) (i : ι) :
    (energyNorm (fiber S label i) ^ (1 / 4 : ℝ) *
      weightSquareSum S (componentWeight label w i) ^ (1 / 2 : ℝ)) ^ 4 =
      energyNorm (fiber S label i) * weightSquareSum S (componentWeight label w i) ^ 2 := by
  rw [mul_pow, ← Real.rpow_mul_natCast (energyNorm_nonneg _),
    ← Real.rpow_mul_natCast (weightSquareSum_nonneg _ _)]
  norm_num

/-- Every component's actual norm bounds the energy of the restricted
parent weight, without an optimality assumption on that restriction. -/
theorem separated_energy_le_component_norms {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) (w : G → ℝ) :
    weightedEnergy S w ≤ (∑ i, (energyNorm (fiber S label i) ^ (1 / 4 : ℝ) *
      weightSquareSum S (componentWeight label w i) ^ (1 / 2 : ℝ)) ^ (20 / 13 : ℝ)) ^ (13 / 5 : ℝ) := by
  apply separated_energy_rational_bound hsep
  · intro i
    exact mul_nonneg (Real.rpow_nonneg (energyNorm_nonneg _) _)
      (Real.rpow_nonneg (weightSquareSum_nonneg _ _) _)
  · intro i
    rw [component_fourth_power]
    exact componentWeight_energy_bound S label w i

end
end Erdos539Geometry
