/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryOptimizedProfile

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance geometricFiberImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- Energy of the square root of the actual conditional endpoint law,
without replacing that law by a fiber optimizer. -/
def imageConditionalEnergy (S : Finset G) (φ : G → H) (ν : S → ℝ) (y : S.image φ) : ℝ :=
  weightedEnergy (fiber S φ y.val)
    (extendWeight (fiber S φ y.val) (fun x ↦ Real.sqrt (imageFiberReference S φ ν y x)))

theorem imageConditionalEnergy_bounds {S : Finset G} (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (y : S.image φ) (hy : finitePush ν (imageEndpoint S φ) y ≠ 0) :
    1 ≤ imageConditionalEnergy S φ ν y ∧ imageConditionalEnergy S φ ν y ≤ energyNorm (fiber S φ y.val) := by
  have hunit : (fun x ↦ Real.sqrt (imageFiberReference S φ ν y x)) ∈ admissibleWeights (fiber S φ y.val) := by
    refine ⟨fun x ↦ Real.sqrt_nonneg _, ?_⟩
    simp_rw [Real.sq_sqrt (imageFiberReference_nonneg S φ ν hν y _)]
    exact imageFiberReference_sum_of_mass_ne_zero S φ ν y hy
  have h := weightedEnergy_ge_squareSum_sq (fiber S φ y.val)
    (extendWeight (fiber S φ y.val) (fun x ↦ Real.sqrt (imageFiberReference S φ ν y x)))
  rw [weightSquareSum_extend, hunit.2, one_pow] at h
  exact ⟨h, energyNorm_ge_admissible hunit⟩

theorem meanFiberProfile_le_logEnergy {S : Finset G} (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) :
    (∑ y, finitePush ν (imageEndpoint S φ) y * stationaryEnergyProfile (fiber S φ y.val) (imageFiberReference S φ ν y)) ≤
      ∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (imageConditionalEnergy S φ ν y) := by
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : finitePush ν (imageEndpoint S φ) y = 0
  · simp only [hy, zero_mul, le_refl]
  exact mul_le_mul_of_nonneg_left
    (stationaryEnergyProfile_le_log_energy (imageFiberReference_nonneg S φ ν hν y)
      (imageFiberReference_sum_of_mass_ne_zero S φ ν y hy))
    (finitePush_nonneg ν (imageEndpoint S φ) hν y)

theorem meanFiberLogEnergy_le_logNorm {S : Finset G} (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) :
    (∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (imageConditionalEnergy S φ ν y)) ≤
      ∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (energyNorm (fiber S φ y.val)) := by
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : finitePush ν (imageEndpoint S φ) y = 0
  · simp only [hy, zero_mul, le_refl]
  have h := imageConditionalEnergy_bounds φ ν hν y hy
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (lt_of_lt_of_le zero_lt_one h.1) h.2)
    (finitePush_nonneg ν (imageEndpoint S φ) hν y)

/-- The sharper bound uses the entropy of the literal projected parent
quadruple, preserving that parent's exact optimizing law. -/
theorem optimizer_meanFiberLogEnergy_lower {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (φ : G → H) :
    Real.log (energyNorm S) -
      (finiteEntropy ((optimizerStationaryAdditiveLaw hS hf hE).imageFlat φ) -
        2 * finiteEntropy (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ))) ≤
      ∑ y, finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y *
        Real.log (imageConditionalEnergy S φ (fun x ↦ f x ^ 2) y) := by
  have h := (optimizerStationaryAdditiveLaw hS hf hE).energyProfile_image_fibring
    (fun x ↦ sq_nonneg (f x)) hf.2 φ
  rw [optimizerStationaryAdditiveLaw_energyProfile hS hf hE] at h
  have hmean := meanFiberProfile_le_logEnergy φ (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x))
  linarith

theorem optimizer_meanFiberLogNorm_lower {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (φ : G → H) :
    Real.log (energyNorm S) -
      (finiteEntropy ((optimizerStationaryAdditiveLaw hS hf hE).imageFlat φ) -
        2 * finiteEntropy (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ))) ≤
      ∑ y, finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y * Real.log (energyNorm (fiber S φ y.val)) :=
  (optimizer_meanFiberLogEnergy_lower hS hf hE φ).trans
    (meanFiberLogEnergy_le_logNorm φ (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)))

variable [AddCommGroup H]

theorem optimizer_meanFiberLogEnergy_lower_optimized {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (φ : G →+ H) :
    Real.log (energyNorm S) - stationaryEnergyProfile (S.image φ) (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ)) ≤
      ∑ y, finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y * Real.log (imageConditionalEnergy S φ (fun x ↦ f x ^ 2) y) := by
  have h := stationaryEnergyProfile_subadditive (fun x ↦ sq_nonneg (f x)) hf.2 φ
  rw [stationaryEnergyProfile_optimizer hS hf hE] at h
  have hmean := meanFiberProfile_le_logEnergy φ (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x))
  linarith

/-- The literal weighted geometric mean, with zero-mass fibers contributing
the factor one, retains the parent norm with the optimized projection cost. -/
theorem optimizer_fiberEnergy_geometric_mean {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (φ : G →+ H) :
    energyNorm S * Real.exp (-stationaryEnergyProfile (S.image φ) (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ))) ≤
      ∏ y, imageConditionalEnergy S φ (fun x ↦ f x ^ 2) y ^ finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y := by
  have h := Real.exp_le_exp.mpr (optimizer_meanFiberLogEnergy_lower_optimized hS hf hE φ)
  have hΛ : 0 < energyNorm S := lt_of_lt_of_le zero_lt_one (one_le_energyNorm hS)
  rw [Real.exp_sub, Real.exp_log hΛ] at h
  have hprod : (∏ y, imageConditionalEnergy S φ (fun x ↦ f x ^ 2) y ^
      finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y) =
      Real.exp (∑ y, finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y *
        Real.log (imageConditionalEnergy S φ (fun x ↦ f x ^ 2) y)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro y _
    by_cases hy : finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y = 0
    · simp only [hy, Real.rpow_zero, zero_mul, Real.exp_zero]
    have he := (imageConditionalEnergy_bounds φ (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)) y hy).1
    rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one he), mul_comm]
  rw [hprod, Real.exp_neg]
  simpa only [div_eq_mul_inv] using h

end
end Erdos539Geometry
