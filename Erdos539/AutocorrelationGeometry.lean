/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CorrelationPairings

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def normalizedAutocorrelation (S : Finset G) (f : G → ℝ) (z : G) : ℝ :=
  weightedCorrelation S f f z / Real.sqrt (weightedEnergy S f)

def autocorrelationCosine (S : Finset G) (f g : G → ℝ) : ℝ :=
  ∑ z ∈ S - S, normalizedAutocorrelation S f z * normalizedAutocorrelation S g z

def autocorrelationDistanceSq (S : Finset G) (f g : G → ℝ) : ℝ :=
  ∑ z ∈ S - S, (normalizedAutocorrelation S f z - normalizedAutocorrelation S g z) ^ 2

theorem autocorrelation_squareSum (S : Finset G) (f : G → ℝ) :
    (∑ z ∈ S - S, weightedCorrelation S f f z ^ 2) = weightedEnergy S f := by
  simpa only [differenceMixedEnergy, pow_two] using differenceMixedEnergy_self S f

theorem normalizedAutocorrelation_unit (S : Finset G) (f : G → ℝ) (hf : 0 < weightedEnergy S f) :
    (∑ z ∈ S - S, normalizedAutocorrelation S f z ^ 2) = 1 := by
  simp only [normalizedAutocorrelation, div_pow, Real.sq_sqrt hf.le]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [autocorrelation_squareSum, mul_inv_cancel₀ hf.ne']

theorem autocorrelationCosine_eq (S : Finset G) (f g : G → ℝ) :
    autocorrelationCosine S f g =
      autocorrelationInner S f g / (Real.sqrt (weightedEnergy S f) * Real.sqrt (weightedEnergy S g)) := by
  simp only [autocorrelationCosine, normalizedAutocorrelation, div_mul_div_comm]
  simp only [autocorrelationInner, differenceMixedEnergy, div_eq_mul_inv, ← Finset.sum_mul]

theorem autocorrelationCosine_nonneg (S : Finset G) (f g : G → ℝ) : 0 ≤ autocorrelationCosine S f g := by
  rw [autocorrelationCosine_eq]
  exact div_nonneg (autocorrelationInner_nonneg S f g) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem autocorrelationCosine_le_one (S : Finset G) (f g : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g) : autocorrelationCosine S f g ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (S - S) (normalizedAutocorrelation S f) (normalizedAutocorrelation S g)
  rw [normalizedAutocorrelation_unit S f hf, normalizedAutocorrelation_unit S g hg, one_mul] at h
  change autocorrelationCosine S f g ^ 2 ≤ 1 at h
  nlinarith

theorem autocorrelationDistanceSq_eq (S : Finset G) (f g : G → ℝ)
    (hf : 0 < weightedEnergy S f) (hg : 0 < weightedEnergy S g) :
    autocorrelationDistanceSq S f g = 2 - 2 * autocorrelationCosine S f g := by
  have hpoint (z : G) : (normalizedAutocorrelation S f z - normalizedAutocorrelation S g z) ^ 2 =
      normalizedAutocorrelation S f z ^ 2 + normalizedAutocorrelation S g z ^ 2 -
        2 * (normalizedAutocorrelation S f z * normalizedAutocorrelation S g z) := by ring
  simp only [autocorrelationDistanceSq, hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, normalizedAutocorrelation_unit S f hf, normalizedAutocorrelation_unit S g hg]
  norm_num [autocorrelationCosine]

theorem autocorrelationDistanceSq_nonneg (S : Finset G) (f g : G → ℝ) :
    0 ≤ autocorrelationDistanceSq S f g := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem autocorrelationDistanceSq_comm (S : Finset G) (f g : G → ℝ) :
    autocorrelationDistanceSq S f g = autocorrelationDistanceSq S g f := by
  simp only [autocorrelationDistanceSq, sub_sq_comm]

end
end Erdos539Geometry
