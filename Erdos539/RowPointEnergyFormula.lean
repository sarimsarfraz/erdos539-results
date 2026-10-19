/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RowPointEnergy
import Erdos539.CorrelationPairings

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem mixedWeightedEnergy_swap_left (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k = mixedWeightedEnergy S g f h k := by
  simp only [mixedWeightedEnergy, weightedConvolution_comm S f g]

/-- Exact raw energy of an arbitrary weighted row and an extra point.
This statement makes no parent maximizing assumption. -/
theorem rowPointSupport_energy (S : Finset G) (h0 : (0 : G) ∈ S) (f : G → ℝ) (r : ℝ) :
    weightedEnergy (rowPointSupport S) (rowPointWeight f r) =
      weightedEnergy S f + 4 * r ^ 2 * weightSquareSum S f + r ^ 4 := by
  rw [weightedEnergy_support (rowPointSupport_subset S h0) _ (rowPointWeight_zero S f r)]
  have h₁ := mixedWeightedEnergy_point_cross S h0 f r
  have h₂ : mixedWeightedEnergy S f (rowPointAtomWeight r) (rowPointAtomWeight r) f = r ^ 2 * weightSquareSum S f := by
    rw [mixedWeightedEnergy_swap_right, h₁]
  have h₃ : mixedWeightedEnergy S (rowPointAtomWeight r) f f (rowPointAtomWeight r) = r ^ 2 * weightSquareSum S f := by
    rw [mixedWeightedEnergy_swap_left, h₁]
  have h₄ : mixedWeightedEnergy S (rowPointAtomWeight r) f (rowPointAtomWeight r) f = r ^ 2 * weightSquareSum S f := by
    rw [mixedWeightedEnergy_swap_left, h₂]
  norm_num [weightedEnergy_product_rows, rowPointWeight, mixedWeightedEnergy_self,
    h₁, h₂, h₃, h₄, weightedEnergy_point S h0]
  ring

theorem rowPointSupport_squareSum (S : Finset G) (h0 : (0 : G) ∈ S) (f : G → ℝ) (r : ℝ) :
    weightSquareSum (rowPointSupport S) (rowPointWeight f r) = weightSquareSum S f + r ^ 2 := by
  rw [weightSquareSum_support (rowPointSupport_subset S h0) _ (rowPointWeight_zero S f r)]
  simp [weightSquareSum, Finset.sum_product, rowPointWeight, rowPointAtomWeight, h0, Finset.sum_add_distrib]

end
end Erdos539Geometry
