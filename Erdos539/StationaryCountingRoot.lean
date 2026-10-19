/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryReferenceFibring
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The uniform-reference Gibbs law is literally uniform on the actual
additive quadruples, with normalizing constant the counting energy. -/
theorem referenceGibbs_uniform_mass {S : Finset G} (hS : S.Nonempty) (a b c d : S) :
    (referenceGibbsLaw S (uniformReference S) (uniformReference_pos hS)).mass a b c d =
      if a.val + b.val = c.val + d.val then 1 / countingEnergy S else 0 := by
  let c₀ : ℝ := (1 / (S.card : ℝ)) ^ (3 / 4 : ℝ)
  have hc : 0 < c₀ := Real.rpow_pos_of_pos (uniformReference_pos hS a) _
  change weightedGibbsMass S (fun _ ↦ c₀) a b c d = _
  rw [weightedGibbsMass, weightedGibbsPartition_constant]
  unfold additiveQuadrupleWeight
  split_ifs
  · field_simp [hc.ne']
  · simp

theorem referenceEndpoint_uniform_eq_counting {S : Finset G} (hS : S.Nonempty) :
    referenceEndpoint S (uniformReference S) = weightedGibbsEndpoint S (fun _ ↦ 1) := by
  funext a
  change (∑ b, ∑ c, ∑ d, (referenceGibbsLaw S (uniformReference S) (uniformReference_pos hS)).mass a b c d) = _
  simp only [referenceGibbs_uniform_mass hS, weightedGibbsEndpoint, weightedGibbsMass,
    additiveQuadrupleWeight, weightedGibbsPartition_constant, one_mul, one_pow]
  simp only [ite_div, zero_div]

/-- Exact maximum entropy for the endpoint of the uniform additive law. -/
theorem stationaryAdditiveEntropy_counting {S : Finset G} (hS : S.Nonempty) :
    stationaryAdditiveEntropy S (referenceEndpoint S (uniformReference S)) = Real.log (countingEnergy S) := by
  rw [referenceEndpoint_uniform_eq_counting hS]
  have hZ : 0 < weightedGibbsPartition S (fun _ ↦ 1) := weightedGibbsPartition_pos hS (fun _ ↦ zero_lt_one)
  rw [stationaryAdditiveEntropy_eq_of_maximal _ (weightedGibbs_entropy_maximal (fun _ ↦ zero_lt_one) hZ),
    weightedGibbs_entropy (fun _ ↦ zero_lt_one) hZ]
  simp only [weightedGibbsPartition_constant, one_pow, one_mul, Real.log_one, mul_zero,
    Finset.sum_const_zero, sub_zero]

/-- The fixed original endpoint and uniform reference start at the exact
ordinary counting-energy defect k(S), rather than a newly reflected parent. -/
theorem stationaryReferenceDefect_counting {S : Finset G} (hS : S.Nonempty) :
    stationaryReferenceDefect S (referenceEndpoint S (uniformReference S)) (uniformReference S) =
      Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) := by
  rw [stationaryReferenceDefect_referenceEndpoint hS (uniformReference_pos hS), referenceDeficit_uniform hS]

theorem counting_endpoint_KL_budget {S : Finset G} (hS : S.Nonempty) :
    3 * finiteRelEntropy (referenceEndpoint S (uniformReference S)) (uniformReference S) ≤
      Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) := by
  have h := (stationaryEntropyDefect_bounds S (referenceEndpoint S (uniformReference S))
    (fun x ↦ (referenceEndpoint_pos hS (uniformReference_pos hS) x).le)
    (referenceEndpoint_sum hS (uniformReference_pos hS))).1
  have he := stationaryReferenceDefect_counting hS
  unfold stationaryReferenceDefect at he
  linarith

end
end Erdos539Geometry
