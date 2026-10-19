/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ComponentNormWeights
import Erdos539.RationalComponentHolder

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]

/-- Rational norm aggregation for the literal separated components of
an arbitrary finite additive support. Separation is an explicit geometric
hypothesis, not a property assigned to arbitrary partitions. -/
theorem energyNorm_separated_rational {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) :
    energyNorm S ^ (5 / 3 : ℝ) ≤ ∑ i, energyNorm (fiber S label i) ^ (5 / 3 : ℝ) := by
  by_cases hS : S.Nonempty
  · obtain ⟨f, hf, hunit, hE⟩ := energyNorm_attained hS
    let w := extendWeight S f
    let p := fun i ↦ weightSquareSum S (componentWeight label w i)
    let σ := fun i ↦ energyNorm (fiber S label i)
    have hp : ∀ i, 0 ≤ p i := fun i ↦ weightSquareSum_nonneg _ _
    have hσ : ∀ i, 0 ≤ σ i := fun i ↦ energyNorm_nonneg _
    have hpsum : ∑ i, p i = 1 := by
      rw [componentWeight_squareSum_total, weightSquareSum_extend, hunit]
    have he := separated_energy_le_component_norms hsep w
    have hholder := rational_component_holder p σ hp hσ hpsum
    have hn : energyNorm S ≤ (∑ i, σ i ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) := by
      rw [← hE]
      exact he.trans hholder
    have hsum : 0 ≤ ∑ i, σ i ^ (5 / 3 : ℝ) :=
      Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (hσ i) _)
    have hpow := Real.rpow_le_rpow (energyNorm_nonneg S) hn (by norm_num : (0 : ℝ) ≤ 5 / 3)
    rw [← Real.rpow_mul hsum] at hpow
    norm_num at hpow
    exact hpow
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, energyNorm_empty]
    norm_num
    exact Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (energyNorm_nonneg _) _)

end
end Erdos539Geometry
