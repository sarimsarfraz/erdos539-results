/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyVariation

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def pointWeight (a : G) (x : G) : ℝ := if x = a then 1 else 0

theorem crossWeightedEnergy_point {S : Finset G} {a : G} (ha : a ∈ S) (f : G → ℝ) :
    mixedWeightedEnergy S f (pointWeight a) f (pointWeight a) = weightSquareSum S f := by
  calc
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ∑ w ∈ S,
        if y = a then if w = a then if x = z then f x * f z else 0 else 0 else 0 := by
      rw [mixedWeightedEnergy_eq_quadruples]
      simp only [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      by_cases hy : y = a <;> by_cases hw : w = a <;> simp [pointWeight, hy, hw]
    _ = _ := by simp [ha, weightSquareSum, pow_two]

omit [AddCommGroup G] in
theorem extendWeight_point {S : Finset G} (a : S) :
    extendWeight S (fun x : S ↦ pointWeight a.val x.val) = pointWeight a.val := by
  funext x
  by_cases hx : x ∈ S
  · simp only [extendWeight, dif_pos hx]
  · have hxa : x ≠ a.val := fun h ↦ hx (h ▸ a.property)
    simp only [extendWeight, dif_neg hx, pointWeight, if_neg hxa]

omit [AddCommGroup G] in
theorem inner_pointWeight (S : Finset G) (f : S → ℝ) (a : S) :
    (∑ x : S, f x * pointWeight a.val x.val) = f a := by
  have he : (fun x : S ↦ pointWeight a.val x.val) = fun x : S ↦ if x = a then (1 : ℝ) else 0 := by
    funext x
    simp only [pointWeight, Subtype.ext_iff]
  change (∑ x : S, f x * (fun y : S ↦ pointWeight a.val y.val) x) = _
  rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Every atom of an exact optimizer's squared-weight law has mass at most
the reciprocal energy norm. No positivity-at-each-point hypothesis is used. -/
theorem energyMaximizer_atom_bound {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (a : S) : f a ^ 2 ≤ 1 / energyNorm S := by
  let g : S → ℝ := fun x ↦ pointWeight a.val x.val
  have hstat := energyMaximizer_stationary hf hE g
  have hinner : (∑ x : S, f x * g x) = f a := inner_pointWeight S f a
  rw [hinner] at hstat
  have h := mixedWeightedEnergy_sq_le S (extendWeight S f) (extendWeight S f)
    (extendWeight S f) (extendWeight S g)
  rw [hstat, mixedWeightedEnergy_self, hE] at h
  have hext : extendWeight S g = pointWeight a.val := extendWeight_point a
  rw [hext, crossWeightedEnergy_point a.property, weightSquareSum_extend, hf.2, mul_one] at h
  have hNormPos := energyNorm_pos hS
  apply (le_div_iff₀ hNormPos).mpr
  apply (mul_le_mul_iff_right₀ hNormPos).mp
  nlinarith

end
end Erdos539Geometry
