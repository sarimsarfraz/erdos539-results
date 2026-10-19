/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ComponentNormWeights
import Erdos539.SharpComponentHolder

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]

/-- The sharp Sidon inequality applied to actual separated component
energies. The additive separation premise includes diagonal pairs. -/
theorem separated_energy_sharp_bound {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) (w : G → ℝ) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (henergy : ∀ i, weightedEnergy S (componentWeight label w i) ≤ v i ^ 4) :
    weightedEnergy S w ≤ (∑ i, v i ^ (4 / sharpSidonExponent)) ^ sharpSidonExponent := by
  exact (separated_energy_le_label_expression hsep w v hv henergy).trans
    (sharp_sidon_energy_bound Finset.univ v (fun i _ ↦ hv i))

theorem separated_energy_le_component_norms_sharp {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) (w : G → ℝ) :
    weightedEnergy S w ≤ (∑ i, (energyNorm (fiber S label i) ^ (1 / 4 : ℝ) *
      weightSquareSum S (componentWeight label w i) ^ (1 / 2 : ℝ)) ^ (4 / sharpSidonExponent)) ^ sharpSidonExponent := by
  apply separated_energy_sharp_bound hsep
  · intro i
    exact mul_nonneg (Real.rpow_nonneg (energyNorm_nonneg _) _)
      (Real.rpow_nonneg (weightSquareSum_nonneg _ _) _)
  · intro i
    rw [component_fourth_power]
    exact componentWeight_energy_bound S label w i

/-- Sharp norm aggregation with r = 1/(log_2(6)-2), for the literal
label fibers of an arbitrary finite separated support. -/
theorem energyNorm_separated_sharp {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) :
    energyNorm S ^ sharpSeparatedExponent ≤ ∑ i, energyNorm (fiber S label i) ^ sharpSeparatedExponent := by
  have hr : 0 < sharpSeparatedExponent := zero_lt_one.trans sharpSeparatedExponent_gt_one
  by_cases hS : S.Nonempty
  · obtain ⟨f, hf, hunit, hE⟩ := energyNorm_attained hS
    let w := extendWeight S f
    let p := fun i ↦ weightSquareSum S (componentWeight label w i)
    let σ := fun i ↦ energyNorm (fiber S label i)
    have hp : ∀ i, 0 ≤ p i := fun i ↦ weightSquareSum_nonneg _ _
    have hσ : ∀ i, 0 ≤ σ i := fun i ↦ energyNorm_nonneg _
    have hpsum : ∑ i, p i = 1 := by
      rw [componentWeight_squareSum_total, weightSquareSum_extend, hunit]
    have he := separated_energy_le_component_norms_sharp hsep w
    have hholder := sharp_component_holder p σ hp hσ hpsum
    have hn : energyNorm S ≤ (∑ i, σ i ^ sharpSeparatedExponent) ^ (sharpSidonExponent - 2) := by
      rw [← hE]
      exact he.trans hholder
    have hsum : 0 ≤ ∑ i, σ i ^ sharpSeparatedExponent :=
      Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (hσ i) _)
    have hpow := Real.rpow_le_rpow (energyNorm_nonneg S) hn hr.le
    rw [← Real.rpow_mul hsum] at hpow
    have hexp : (sharpSidonExponent - 2) * sharpSeparatedExponent = 1 := by
      unfold sharpSeparatedExponent
      exact mul_one_div_cancel (sub_pos.mpr sharpSidonExponent_strict_bounds.1).ne'
    rwa [hexp, Real.rpow_one] at hpow
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, energyNorm_empty, Real.zero_rpow hr.ne']
    exact Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (energyNorm_nonneg _) _)

end
end Erdos539Geometry
