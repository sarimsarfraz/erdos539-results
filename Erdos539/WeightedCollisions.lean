/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedEnergyBasics

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

/-- Weighted collisions can be counted by fibers or by ordered pairs. -/
theorem weighted_fiber_collision {α β : Type*} [DecidableEq β] (U : Finset α) (T : Finset β)
    (f : α → β) (w v : α → ℝ) (hm : ∀ x ∈ U, f x ∈ T) :
    (∑ b ∈ T, (∑ x ∈ fiber U f b, w x) * (∑ y ∈ fiber U f b, v y)) =
      ∑ x ∈ U, ∑ y ∈ U, if f x = f y then w x * v y else 0 := by
  calc
    _ = ∑ b ∈ T, ∑ x ∈ fiber U f b, w x * (∑ y ∈ fiber U f b, v y) := by
      simp_rw [Finset.sum_mul]
    _ = ∑ b ∈ T, ∑ x ∈ fiber U f b,
        w x * (∑ y ∈ U, if f x = f y then v y else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro x hx
      rw [(mem_fiber.mp hx).2]
      simp only [fiber, Finset.sum_filter, eq_comm]
    _ = ∑ x ∈ U, w x * (∑ y ∈ U, if f x = f y then v y else 0) := by
      exact @Finset.sum_fiberwise_of_maps_to α β ℝ _ U T (Classical.decEq β) f hm _
    _ = _ := by simp_rw [Finset.mul_sum, mul_ite, mul_zero]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Literal additive-quadruple formula for the convolution-based definition. -/
theorem weightedEnergy_eq_quadruples (S : Finset G) (f : G → ℝ) :
    weightedEnergy S f = ∑ p ∈ S ×ˢ S, ∑ q ∈ S ×ˢ S,
      if p.1 + p.2 = q.1 + q.2 then (f p.1 * f p.2) * (f q.1 * f q.2) else 0 := by
  unfold weightedEnergy
  simp only [pow_two, weightedConvolution]
  apply weighted_fiber_collision
  intro p hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  exact Finset.mem_add.mpr ⟨p.1, ha, p.2, hb, rfl⟩

def mixedWeightedEnergy (S : Finset G) (f g h k : G → ℝ) : ℝ :=
  ∑ z ∈ S + S, weightedConvolution S f g z * weightedConvolution S h k z

theorem mixedWeightedEnergy_eq_quadruples (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k = ∑ p ∈ S ×ˢ S, ∑ q ∈ S ×ˢ S,
      if p.1 + p.2 = q.1 + q.2 then (f p.1 * g p.2) * (h q.1 * k q.2) else 0 := by
  apply weighted_fiber_collision
  intro p hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  exact Finset.mem_add.mpr ⟨p.1, ha, p.2, hb, rfl⟩

theorem mixedWeightedEnergy_self (S : Finset G) (f : G → ℝ) :
    mixedWeightedEnergy S f f f f = weightedEnergy S f := by
  simp only [mixedWeightedEnergy, weightedEnergy, pow_two]

/-- The first of the two finite Cauchy-Schwarz steps in mixed-energy Holder. -/
theorem mixedWeightedEnergy_sq_le (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k ^ 2 ≤
      mixedWeightedEnergy S f g f g * mixedWeightedEnergy S h k h k := by
  simpa only [mixedWeightedEnergy, ← pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq (S + S) (weightedConvolution S f g) (weightedConvolution S h k)

end
end Erdos539Geometry
