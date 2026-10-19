/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]

omit [DecidableEq G] in
theorem weightedConvolution_sum_left (S : Finset G) (f : ι → G → ℝ) (g : G → ℝ) (z : G) :
    weightedConvolution S (fun x ↦ ∑ i, f i x) g z = ∑ i, weightedConvolution S (f i) g z := by
  simp only [weightedConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq G] in
theorem weightedConvolution_sum_right (S : Finset G) (f : G → ℝ) (g : ι → G → ℝ) (z : G) :
    weightedConvolution S f (fun x ↦ ∑ i, g i x) z = ∑ i, weightedConvolution S f (g i) z := by
  simp only [weightedConvolution, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mixedWeightedEnergy_sum_first (S : Finset G) (f : ι → G → ℝ) (g h k : G → ℝ) :
    mixedWeightedEnergy S (fun x ↦ ∑ i, f i x) g h k = ∑ i, mixedWeightedEnergy S (f i) g h k := by
  simp only [mixedWeightedEnergy, weightedConvolution_sum_left, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem mixedWeightedEnergy_sum_second (S : Finset G) (f : G → ℝ) (g : ι → G → ℝ) (h k : G → ℝ) :
    mixedWeightedEnergy S f (fun x ↦ ∑ i, g i x) h k = ∑ i, mixedWeightedEnergy S f (g i) h k := by
  simp only [mixedWeightedEnergy, weightedConvolution_sum_right, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem mixedWeightedEnergy_sum_third (S : Finset G) (f g : G → ℝ) (h : ι → G → ℝ) (k : G → ℝ) :
    mixedWeightedEnergy S f g (fun x ↦ ∑ i, h i x) k = ∑ i, mixedWeightedEnergy S f g (h i) k := by
  simp only [mixedWeightedEnergy, weightedConvolution_sum_left, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mixedWeightedEnergy_sum_fourth (S : Finset G) (f g h : G → ℝ) (k : ι → G → ℝ) :
    mixedWeightedEnergy S f g h (fun x ↦ ∑ i, k i x) = ∑ i, mixedWeightedEnergy S f g h (k i) := by
  simp only [mixedWeightedEnergy, weightedConvolution_sum_right, Finset.mul_sum]
  rw [Finset.sum_comm]

end
end Erdos539Geometry
