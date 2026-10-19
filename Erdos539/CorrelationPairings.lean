/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedHolder
import Erdos539.ConvolutionAlgebra

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Re-pair all four weights between additive sums and differences. -/
theorem differenceMixedEnergy_eq_mixed (S : Finset G) (f g h k : G → ℝ) :
    differenceMixedEnergy S f g h k = mixedWeightedEnergy S f k h g := by
  rw [differenceMixedEnergy_eq_quadruples, mixedWeightedEnergy_eq_quadruples]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  have hrel : a - b = c - d ↔ a + d = c + b := sub_eq_sub_iff_add_eq_add
  by_cases he : a - b = c - d
  · simp only [if_pos he, if_pos (hrel.mp he)]
    ring
  · simp only [if_neg he, if_neg (mt hrel.mpr he)]

theorem differenceMixedEnergy_sq_le (S : Finset G) (f g h k : G → ℝ) :
    differenceMixedEnergy S f g h k ^ 2 ≤
      differenceMixedEnergy S f g f g * differenceMixedEnergy S h k h k := by
  simpa only [differenceMixedEnergy, ← pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq (S - S) (weightedCorrelation S f g) (weightedCorrelation S h k)

theorem mixedWeightedEnergy_swap_right (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k = mixedWeightedEnergy S f g k h := by
  simp only [mixedWeightedEnergy, weightedConvolution_comm S h k]

def autocorrelationInner (S : Finset G) (f g : G → ℝ) : ℝ := differenceMixedEnergy S f f g g

theorem autocorrelationInner_nonneg (S : Finset G) (f g : G → ℝ) : 0 ≤ autocorrelationInner S f g := by
  rw [autocorrelationInner, ← mixedWeightedEnergy_repair]
  exact crossWeightedEnergy_nonneg S f g

theorem autocorrelationInner_comm (S : Finset G) (f g : G → ℝ) :
    autocorrelationInner S f g = autocorrelationInner S g f := by
  simp only [autocorrelationInner, differenceMixedEnergy, mul_comm]

/-- Each of the three pairings bounds the same literal mixed energy. -/
theorem mixedEnergy_pairing12 (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k ^ 2 ≤ autocorrelationInner S f g * autocorrelationInner S h k := by
  simpa only [mixedWeightedEnergy_repair, autocorrelationInner] using mixedWeightedEnergy_sq_le S f g h k

theorem mixedEnergy_pairing14 (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k ^ 2 ≤ autocorrelationInner S f k * autocorrelationInner S h g := by
  have hh := differenceMixedEnergy_sq_le S f k h g
  simp only [differenceMixedEnergy_eq_mixed] at hh
  rw [mixedWeightedEnergy_repair, mixedWeightedEnergy_repair] at hh
  exact hh

theorem mixedEnergy_pairing13 (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k ^ 2 ≤ autocorrelationInner S f h * autocorrelationInner S g k := by
  rw [mixedWeightedEnergy_swap_right]
  have hh := mixedEnergy_pairing14 S f g k h
  rw [autocorrelationInner_comm S k g] at hh
  exact hh

end
end Erdos539Geometry
