/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RowPointReference

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem rowPointReference_admissible (S : Finset G) (h0 : (0 : G) ∈ S) :
    (fun x ↦ Real.sqrt (rowPointReference S x)) ∈ admissibleWeights (rowPointSupport S) := by
  refine ⟨fun _ ↦ Real.sqrt_nonneg _, ?_⟩
  simp_rw [Real.sq_sqrt (rowPointReference_nonneg S _)]
  exact rowPointReference_sum S h0

theorem rowPointReference_energy (S : Finset G) (h0 : (0 : G) ∈ S) :
    weightedEnergy (rowPointSupport S)
      (extendWeight (rowPointSupport S) (fun x ↦ Real.sqrt (rowPointReference S x))) =
      (countingEnergy S / (S.card : ℝ) ^ 2 + 5) / 4 := by
  have he : weightedEnergy (rowPointSupport S)
      (extendWeight (rowPointSupport S) (fun x ↦ Real.sqrt (rowPointReference S x))) =
      weightedEnergy (rowPointSupport S)
        (rowPointWeight (fun _ ↦ Real.sqrt (1 / (2 * (S.card : ℝ)))) (Real.sqrt (1 / 2))) := by
    apply weightedEnergy_congr
    intro x hx
    simp only [extendWeight, dif_pos hx, rowPointReference, rowPointWeight]
    rcases Finset.mem_union.mp hx with hx | hx
    · have hy : x.2 = 0 := Finset.mem_singleton.mp (Finset.mem_product.mp hx).2
      simp [hy]
    · have he : x = (0, 1) := Finset.mem_singleton.mp hx
      simp [he, rowPointAtomWeight]
  rw [he, rowPointSupport_energy S h0]
  have hc (c : ℝ) : weightedEnergy S (fun _ ↦ c) = c ^ 4 * countingEnergy S := by
    simpa only [mul_one, countingEnergy] using weightedEnergy_scale S (fun _ ↦ 1) c
  rw [hc]
  simp only [weightSquareSum, Finset.sum_const, nsmul_eq_mul,
    show (4 : ℕ) = 2 * 2 by decide, pow_mul,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (2 * S.card)),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨0, h0⟩).ne'
  field_simp
  ring

theorem rowPointReference_conditional_energy (S : Finset G) (h0 : (0 : G) ∈ S)
    (y : (rowPointSupport S).image Prod.snd) :
    imageConditionalEnergy (rowPointSupport S) Prod.snd (rowPointReference S) y =
      if y.val = 0 then countingEnergy S / (S.card : ℝ) ^ 2 else 1 := by
  have hy : y.val = 0 ∨ y.val = 1 := by
    simpa only [rowPointSupport_image S h0, Finset.mem_insert, Finset.mem_singleton] using y.property
  rw [imageConditionalEnergy, rowPointReference_conditional S h0,
    sqrt_uniformReference, uniformEnergyWeight_energy]
  rcases hy with hy | hy
  · rw [hy, rowPointSupport_fiber_zero, countingEnergy_product, countingEnergy_singleton]
    simp
  · rw [hy, rowPointSupport_fiber_one, countingEnergy_singleton]
    norm_num

end
end Erdos539Geometry
