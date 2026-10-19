/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedGibbsLaw

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem additiveQuadrupleWeight_scale (S : Finset G) (f : S → ℝ) (t : ℝ) (a b c d : S) :
    additiveQuadrupleWeight S (fun x ↦ t * f x) a b c d = t ^ 4 * additiveQuadrupleWeight S f a b c d := by
  unfold additiveQuadrupleWeight
  split_ifs <;> ring

theorem weightedGibbsPartition_scale (S : Finset G) (f : S → ℝ) (t : ℝ) :
    weightedGibbsPartition S (fun x ↦ t * f x) = t ^ 4 * weightedGibbsPartition S f := by
  rw [weightedGibbsPartition, extendWeight_scale, weightedEnergy_scale]
  rfl

/-- Scaling a weight by any nonzero scalar preserves its normalized
quadruple distribution, including a zero partition function. -/
theorem weightedGibbsMass_scale (S : Finset G) (f : S → ℝ) {t : ℝ} (ht : t ≠ 0) (a b c d : S) :
    weightedGibbsMass S (fun x ↦ t * f x) a b c d = weightedGibbsMass S f a b c d := by
  rw [weightedGibbsMass, additiveQuadrupleWeight_scale, weightedGibbsPartition_scale]
  exact mul_div_mul_left _ _ (pow_ne_zero 4 ht)

theorem weightedGibbsEndpoint_scale (S : Finset G) (f : S → ℝ) {t : ℝ} (ht : t ≠ 0) :
    weightedGibbsEndpoint S (fun x ↦ t * f x) = weightedGibbsEndpoint S f := by
  funext a
  simp only [weightedGibbsEndpoint, weightedGibbsMass_scale S f ht]

end
end Erdos539Geometry
