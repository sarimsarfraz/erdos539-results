/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiberEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

/-- Exact factorization for literal tensor weights. -/
theorem weightedEnergy_tensor (U : Finset G) (V : Finset H) (f : G → ℝ) (g : H → ℝ) :
    weightedEnergy (U ×ˢ V) (fun x ↦ f x.1 * g x.2) =
      weightedEnergy U f * weightedEnergy V g := by
  rw [weightedEnergy_eq_four_sum, sum_four_products,
    weightedEnergy_eq_four_sum, weightedEnergy_eq_four_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  by_cases h1 : a + b = c + d <;> by_cases h2 : i + j = k + l <;> simp [h1, h2]
  ring

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem weightSquareSum_tensor (U : Finset G) (V : Finset H) (f : G → ℝ) (g : H → ℝ) :
    weightSquareSum (U ×ˢ V) (fun x ↦ f x.1 * g x.2) =
      weightSquareSum U f * weightSquareSum V g := by
  simp only [weightSquareSum, Finset.sum_product, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem weightSquareSum_rowNormWeight (U : Finset G) (V : Finset H) (w : G × H → ℝ) :
    weightSquareSum V (rowNormWeight U w) = weightSquareSum (U ×ˢ V) w := by
  unfold weightSquareSum
  simp only [rowNormWeight, Real.sq_sqrt (weightSquareSum_nonneg _ _)]
  simp only [weightSquareSum, Finset.sum_product]
  exact Finset.sum_comm

/-- Product norm upper bound from the actual row-norm marginal. -/
theorem weightedEnergy_product_norm_bound (U : Finset G) (V : Finset H) (w : G × H → ℝ) :
    weightedEnergy (U ×ˢ V) w ≤ energyNorm U * energyNorm V * weightSquareSum (U ×ˢ V) w ^ 2 := by
  have h := weightedEnergy_product_le_marginal U V w (rowNormWeight U w)
    (energyNorm_nonneg U) (fun v _ ↦ rowNormWeight_nonneg U w v) (by
      intro v _
      rw [rowNormWeight_pow_four]
      exact weightedEnergy_le_norm_squareSum U _)
  have hh := mul_le_mul_of_nonneg_left
    (weightedEnergy_le_norm_squareSum V (rowNormWeight U w)) (energyNorm_nonneg U)
  rw [weightSquareSum_rowNormWeight] at hh
  exact h.trans (by simpa only [mul_assoc] using hh)

/-- Exact multiplicativity of the literal finite energy norm, including
empty factors. Tensor products of attained optimizers supply the lower bound. -/
theorem energyNorm_product (U : Finset G) (V : Finset H) :
    energyNorm (U ×ˢ V) = energyNorm U * energyNorm V := by
  by_cases hU : U.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
  by_cases hV : V.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hV]
  apply le_antisymm
  · obtain ⟨w, _, hw, hE⟩ := energyNorm_attained (hU.product hV)
    have h := weightedEnergy_product_norm_bound U V (extendWeight (U ×ˢ V) w)
    simpa only [hE, weightSquareSum_extend, hw, one_pow, mul_one] using h
  · obtain ⟨f, hf, hfn, hfE⟩ := energyNorm_attained hU
    obtain ⟨g, hg, hgn, hgE⟩ := energyNorm_attained hV
    let w : G × H → ℝ := fun x ↦ extendWeight U f x.1 * extendWeight V g x.2
    have hw : weightSquareSum (U ×ˢ V) w = 1 := by
      rw [weightSquareSum_tensor, weightSquareSum_extend, weightSquareSum_extend, hfn, hgn, one_mul]
    have he : weightedEnergy (U ×ˢ V) w = energyNorm U * energyNorm V := by
      rw [weightedEnergy_tensor, hfE, hgE]
    have h := weightedEnergy_le_norm_squareSum (U ×ˢ V) w
    simpa only [hw, he, one_pow, mul_one] using h

end
end Erdos539Geometry
