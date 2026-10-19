/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryAdditiveLaw

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

omit [DecidableEq G] in
theorem endpoint_expectation (Q : StationaryAdditiveLaw S ν) (g : S → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * (g a + g b + g c + g d)) =
      4 * ∑ a, ν a * g a := by
  have h₁ : (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * g a) = ∑ a, ν a * g a := by
    simp only [← Finset.sum_mul, Q.first]
  have h₂ : (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * g b) = ∑ b, ν b * g b := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Q.second]
  have h₃ : (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * g c) = ∑ c, ν c * g c := by
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Q.third]
  have h₄ : (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * g d) = ∑ d, ν d * g d := by
    conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Q.fourth]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h₁, h₂, h₃, h₄]
  ring

theorem referenceWeight_sum :
    (∑ a, ∑ b, ∑ c, ∑ d, referenceWeight ν a b c d) =
      weightedEnergy S (extendWeight S (fun x ↦ Real.sqrt (ν x))) := by
  unfold referenceWeight additiveQuadrupleWeight
  rw [← mixedWeightedEnergy_subtype]
  exact mixedWeightedEnergy_self _ _

theorem reference_log_sum (Q : StationaryAdditiveLaw S ν) :
    (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * Real.log (referenceWeight ν a b c d)) =
      -2 * finiteEntropy ν := by
  simp only [Q.referenceWeight_log_term, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Q.endpoint_expectation]
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

/-- A stationary additive law controls the energy of its literal
square-root endpoint marginal. This does not require that marginal to
maximize energy and does not replace it by an optimizer. -/
theorem entropy_le_log_energy (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    Q.entropy - 2 * finiteEntropy ν ≤
      Real.log (weightedEnergy S (extendWeight S (fun x ↦ Real.sqrt (ν x)))) := by
  have hunit : weightSquareSum S (extendWeight S (fun x ↦ Real.sqrt (ν x))) = 1 := by
    rw [weightSquareSum_extend]
    simp_rw [Real.sq_sqrt (hν _)]
    exact hs
  have hE := weightedEnergy_ge_squareSum_sq S (extendWeight S (fun x ↦ Real.sqrt (ν x)))
  rw [hunit, one_pow] at hE
  let p : (S × S) × (S × S) → ℝ := fun z ↦ Q.mass z.1.1 z.1.2 z.2.1 z.2.2
  let w : (S × S) × (S × S) → ℝ := fun z ↦ referenceWeight ν z.1.1 z.1.2 z.2.1 z.2.2
  have hps : ∑ z, p z = 1 := by
    simpa only [p, Fintype.sum_prod_type] using Q.total_mass hs
  have hw : 0 < ∑ z, w z := by
    simp only [w, Fintype.sum_prod_type, referenceWeight_sum]
    linarith
  have hg := finiteEntropy_le_log_partition p w
    (fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2) hps
    (fun z ↦ referenceWeight_nonneg z.1.1 z.1.2 z.2.1 z.2.2) hw
    (fun _ hz ↦ Q.referenceWeight_pos hz)
  simp only [finiteEntropy, p, w, Fintype.sum_prod_type] at hg
  rw [referenceWeight_sum, Q.reference_log_sum] at hg
  change Q.entropy ≤ _ at hg
  linarith

theorem entropy_le_log_norm (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    Q.entropy - 2 * finiteEntropy ν ≤ Real.log (energyNorm S) := by
  have hf : (fun x ↦ Real.sqrt (ν x)) ∈ admissibleWeights S := by
    refine ⟨fun _ ↦ Real.sqrt_nonneg _, ?_⟩
    simp_rw [Real.sq_sqrt (hν _)]
    exact hs
  have hE := weightedEnergy_ge_squareSum_sq S (extendWeight S (fun x ↦ Real.sqrt (ν x)))
  rw [weightSquareSum_extend, hf.2, one_pow] at hE
  exact (Q.entropy_le_log_energy hν hs).trans
    (Real.log_le_log (by linarith) (energyNorm_ge_admissible hf))

end StationaryAdditiveLaw
end
end Erdos539Geometry
