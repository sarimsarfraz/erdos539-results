/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedGibbsLaw

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

theorem finiteRelEntropy_eq_entropy_cross {α : Type*} [Fintype α] (p q : α → ℝ) :
    finiteRelEntropy p q = -finiteEntropy p - ∑ x, p x * Real.log (q x) := by
  simp only [finiteRelEntropy, finiteEntropy, Real.negMulLog, mul_sub,
    Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib, neg_neg]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

theorem weightedGibbsMass_pos_of_support (Q : StationaryAdditiveLaw S ν)
    {f : S → ℝ} (hf : ∀ x, 0 < f x) (hZ : 0 < weightedGibbsPartition S f)
    {a b c d : S} (hq : Q.mass a b c d ≠ 0) : 0 < weightedGibbsMass S f a b c d := by
  have hrel : a.val + b.val = c.val + d.val := by
    by_contra hh
    exact hq (Q.supported a b c d hh)
  simp only [weightedGibbsMass, additiveQuadrupleWeight, if_pos hrel]
  exact div_pos (mul_pos (mul_pos (hf a) (hf b)) (mul_pos (hf c) (hf d))) hZ

theorem weightedGibbs_log_term (Q : StationaryAdditiveLaw S ν)
    {f : S → ℝ} (hf : ∀ x, 0 < f x) (hZ : 0 < weightedGibbsPartition S f) (a b c d : S) :
    Q.mass a b c d * Real.log (weightedGibbsMass S f a b c d) =
      Q.mass a b c d * ((Real.log (f a) + Real.log (f b) + Real.log (f c) + Real.log (f d)) -
        Real.log (weightedGibbsPartition S f)) := by
  by_cases hq : Q.mass a b c d = 0
  · simp [hq]
  have hrel : a.val + b.val = c.val + d.val := by
    by_contra hh
    exact hq (Q.supported a b c d hh)
  simp only [weightedGibbsMass, additiveQuadrupleWeight, if_pos hrel]
  rw [Real.log_div (mul_ne_zero (mul_ne_zero (hf a).ne' (hf b).ne')
      (mul_ne_zero (hf c).ne' (hf d).ne')) hZ.ne',
    Real.log_mul (mul_ne_zero (hf a).ne' (hf b).ne') (mul_ne_zero (hf c).ne' (hf d).ne'),
    Real.log_mul (hf a).ne' (hf b).ne', Real.log_mul (hf c).ne' (hf d).ne']
  ring

theorem weightedGibbs_log_expectation (Q : StationaryAdditiveLaw S ν) (hν : ∑ x, ν x = 1)
    {f : S → ℝ} (hf : ∀ x, 0 < f x) (hZ : 0 < weightedGibbsPartition S f) :
    (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * Real.log (weightedGibbsMass S f a b c d)) =
      4 * ∑ x, ν x * Real.log (f x) - Real.log (weightedGibbsPartition S f) := by
  simp_rw [Q.weightedGibbs_log_term hf hZ]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [Q.endpoint_expectation, Q.total_mass hν, one_mul]

/-- The exact relative-entropy gap for every stationary competitor. -/
theorem relativeEntropy_weightedGibbs (Q : StationaryAdditiveLaw S ν) (hν : ∑ x, ν x = 1)
    {f : S → ℝ} (hf : ∀ x, 0 < f x) (hZ : 0 < weightedGibbsPartition S f) :
    finiteRelEntropy Q.flat (weightedGibbsLaw S f (fun x ↦ (hf x).le)).flat =
      -Q.entropy - 4 * ∑ x, ν x * Real.log (f x) + Real.log (weightedGibbsPartition S f) := by
  rw [finiteRelEntropy_eq_entropy_cross]
  have hcross : (∑ z, Q.flat z * Real.log ((weightedGibbsLaw S f (fun x ↦ (hf x).le)).flat z)) =
      4 * ∑ x, ν x * Real.log (f x) - Real.log (weightedGibbsPartition S f) := by
    simpa only [flat, weightedGibbsLaw, Fintype.sum_prod_type] using Q.weightedGibbs_log_expectation hν hf hZ
  rw [hcross]
  have he : finiteEntropy Q.flat = Q.entropy := by
    simp only [finiteEntropy, flat, entropy, Fintype.sum_prod_type]
  rw [he]
  ring

theorem relativeEntropy_weightedGibbs_nonneg (Q : StationaryAdditiveLaw S ν)
    (hν : ∑ x, ν x = 1) {f : S → ℝ} (hf : ∀ x, 0 < f x)
    (hZ : 0 < weightedGibbsPartition S f) :
    0 ≤ finiteRelEntropy Q.flat (weightedGibbsLaw S f (fun x ↦ (hf x).le)).flat := by
  apply finiteRelEntropy_nonneg
  · intro z
    exact Q.nonneg _ _ _ _
  · intro z
    exact weightedGibbsMass_nonneg (fun x ↦ (hf x).le) _ _ _ _
  · simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hν
  · simpa only [flat, Fintype.sum_prod_type] using
      (weightedGibbsLaw S f (fun x ↦ (hf x).le)).total_mass (weightedGibbsEndpoint_sum hZ.ne')
  · intro z hz
    exact Q.weightedGibbsMass_pos_of_support hf hZ hz

end StationaryAdditiveLaw

/-- The Gibbs law's literal entropy identity, without optimizer assumptions. -/
theorem weightedGibbs_entropy {S : Finset G} {f : S → ℝ} (hf : ∀ x, 0 < f x)
    (hZ : 0 < weightedGibbsPartition S f) :
    (weightedGibbsLaw S f (fun x ↦ (hf x).le)).entropy =
      Real.log (weightedGibbsPartition S f) - 4 * ∑ x, weightedGibbsEndpoint S f x * Real.log (f x) := by
  have h := (weightedGibbsLaw S f (fun x ↦ (hf x).le)).relativeEntropy_weightedGibbs
    (weightedGibbsEndpoint_sum hZ.ne') hf hZ
  simp only [finiteRelEntropy, sub_self, mul_zero, Finset.sum_const_zero] at h
  linarith

/-- The recomputed Gibbs law maximizes entropy among all additive laws
with its actual endpoint marginal. -/
theorem weightedGibbs_entropy_maximal {S : Finset G} {f : S → ℝ} (hf : ∀ x, 0 < f x)
    (hZ : 0 < weightedGibbsPartition S f) (Q : StationaryAdditiveLaw S (weightedGibbsEndpoint S f)) :
    Q.entropy ≤ (weightedGibbsLaw S f (fun x ↦ (hf x).le)).entropy := by
  have h := Q.relativeEntropy_weightedGibbs_nonneg (weightedGibbsEndpoint_sum hZ.ne') hf hZ
  rw [Q.relativeEntropy_weightedGibbs (weightedGibbsEndpoint_sum hZ.ne') hf hZ] at h
  rw [weightedGibbs_entropy hf hZ]
  linarith

end
end Erdos539Geometry
