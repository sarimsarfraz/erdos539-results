/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedGibbsEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

theorem four_product_le_fourth_mean (a b c d : ℝ) :
    a * b * c * d ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (c ^ 2 - d ^ 2)]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Fourth-root tilts are controlled by the actual Gibbs endpoint law.
This is an elementary four-term arithmetic-geometric-mean bound, not
an optimizer assumption. -/
theorem weightedGibbsPartition_mul_le {S : Finset G} {f : S → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hZ : 0 < weightedGibbsPartition S f) (g : S → ℝ) :
    weightedGibbsPartition S (fun x ↦ f x * g x) ≤
      weightedGibbsPartition S f * ∑ x, weightedGibbsEndpoint S f x * g x ^ 4 := by
  have hpoint (a b c d : S) :
      additiveQuadrupleWeight S (fun x ↦ f x * g x) a b c d ≤
        weightedGibbsPartition S f * (weightedGibbsMass S f a b c d *
          (g a ^ 4 + g b ^ 4 + g c ^ 4 + g d ^ 4)) / 4 := by
    have hm : weightedGibbsPartition S f * weightedGibbsMass S f a b c d =
        additiveQuadrupleWeight S f a b c d := by
      unfold weightedGibbsMass
      field_simp
    rw [← mul_assoc, hm]
    by_cases he : a.val + b.val = c.val + d.val
    · simp only [additiveQuadrupleWeight, if_pos he]
      have hh := mul_le_mul_of_nonneg_left (four_product_le_fourth_mean (g a) (g b) (g c) (g d))
        (mul_nonneg (mul_nonneg (hf a) (hf b)) (mul_nonneg (hf c) (hf d)))
      nlinarith [hh]
    · simp [additiveQuadrupleWeight, he]
  rw [weightedGibbsPartition_eq_sum]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦
      Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦
        Finset.sum_le_sum (s := Finset.univ) (fun d _ ↦ hpoint a b c d))))
  have havg := (weightedGibbsLaw S f hf).endpoint_expectation (fun x ↦ g x ^ 4)
  simp only [div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul] at h
  change _ ≤ weightedGibbsPartition S f *
    (∑ a, ∑ b, ∑ c, ∑ d, (weightedGibbsLaw S f hf).mass a b c d *
      (g a ^ 4 + g b ^ 4 + g c ^ 4 + g d ^ 4)) * 4⁻¹ at h
  rw [havg] at h
  nlinarith [h]

/-- A positive comparison marginal supplies the fourth-root tilt. -/
def weightedGibbsEndpointTilt (S : Finset G) (f η : S → ℝ) (x : S) : ℝ :=
  f x * (η x / weightedGibbsEndpoint S f x) ^ (1 / 4 : ℝ)

theorem weightedGibbsEndpointTilt_pos {S : Finset G} (hS : S.Nonempty)
    {f η : S → ℝ} (hf : ∀ x, 0 < f x) (hη : ∀ x, 0 < η x) (x : S) :
    0 < weightedGibbsEndpointTilt S f η x :=
  mul_pos (hf x) (Real.rpow_pos_of_pos
    (div_pos (hη x) (weightedGibbsEndpoint_pos hf (weightedGibbsPartition_pos hS hf) x)) _)

/-- Tilting toward any actual positive probability endpoint law does not
increase the partition function. -/
theorem weightedGibbsEndpointTilt_partition_le {S : Finset G} (hS : S.Nonempty)
    {f η : S → ℝ} (hf : ∀ x, 0 < f x) (hη : ∀ x, 0 < η x) (hηs : ∑ x, η x = 1) :
    weightedGibbsPartition S (weightedGibbsEndpointTilt S f η) ≤ weightedGibbsPartition S f := by
  have hZ := weightedGibbsPartition_pos hS hf
  have hpoint (x : S) : weightedGibbsEndpoint S f x *
      ((η x / weightedGibbsEndpoint S f x) ^ (1 / 4 : ℝ)) ^ 4 = η x := by
    have hv := weightedGibbsEndpoint_pos hf hZ x
    rw [← Real.rpow_mul_natCast (div_pos (hη x) hv).le]
    norm_num
    field_simp
  have h := weightedGibbsPartition_mul_le (fun x ↦ (hf x).le) hZ
    (fun x ↦ (η x / weightedGibbsEndpoint S f x) ^ (1 / 4 : ℝ))
  simp_rw [hpoint] at h
  rw [hηs, mul_one] at h
  exact h

theorem weightedGibbsEndpointTilt_log {S : Finset G} (hS : S.Nonempty)
    {f η : S → ℝ} (hf : ∀ x, 0 < f x) (hη : ∀ x, 0 < η x) (x : S) :
    Real.log (weightedGibbsEndpointTilt S f η x) = Real.log (f x) +
      (1 / 4 : ℝ) * (Real.log (η x) - Real.log (weightedGibbsEndpoint S f x)) := by
  have hv := weightedGibbsEndpoint_pos hf (weightedGibbsPartition_pos hS hf) x
  rw [weightedGibbsEndpointTilt, Real.log_mul (hf x).ne' (Real.rpow_pos_of_pos (div_pos (hη x) hv) _).ne',
    Real.log_rpow (div_pos (hη x) hv), Real.log_div (hη x).ne' hv.ne']

end
end Erdos539Geometry
