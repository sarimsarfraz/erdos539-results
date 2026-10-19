/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyMonotonicity

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

theorem sum_four_products {α β : Type*} (U : Finset α) (V : Finset β)
    (F : (α × β) → (α × β) → (α × β) → (α × β) → ℝ) :
    (∑ a ∈ U ×ˢ V, ∑ b ∈ U ×ˢ V, ∑ c ∈ U ×ˢ V, ∑ d ∈ U ×ˢ V, F a b c d) =
      ∑ i ∈ V, ∑ j ∈ V, ∑ k ∈ V, ∑ l ∈ V,
        ∑ a ∈ U, ∑ b ∈ U, ∑ c ∈ U, ∑ d ∈ U, F (a,i) (b,j) (c,k) (d,l) := by
  simp only [Finset.sum_product_right]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; rw [Finset.sum_comm]

variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

theorem weightedEnergy_eq_four_sum (S : Finset G) (f : G → ℝ) :
    weightedEnergy S f = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S,
      if a + b = c + d then (f a * f b) * (f c * f d) else 0 := by
  rw [weightedEnergy_eq_quadruples]
  simp only [Finset.sum_product]

/-- Exact Fubini expansion by four row labels. The rows can have zeros at
arbitrary positions, so this applies to any finite relation in the rectangle. -/
theorem weightedEnergy_product_rows (U : Finset G) (V : Finset H) (w : G × H → ℝ) :
    weightedEnergy (U ×ˢ V) w = ∑ i ∈ V, ∑ j ∈ V, ∑ k ∈ V, ∑ l ∈ V,
      if i + j = k + l then
        mixedWeightedEnergy U (fun a ↦ w (a,i)) (fun a ↦ w (a,j))
          (fun a ↦ w (a,k)) (fun a ↦ w (a,l)) else 0 := by
  rw [weightedEnergy_eq_four_sum, sum_four_products]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hrows : i + j = k + l
  · simp only [Prod.mk_add_mk, Prod.mk.injEq, hrows, and_true, if_true,
      mixedWeightedEnergy_eq_quadruples, Finset.sum_product]
  · simp only [Prod.mk_add_mk, Prod.mk.injEq, hrows, and_false, if_false, Finset.sum_const_zero]

/-- Fiberwise mixed Holder: a uniform row energy bound is multiplied by
the energy of the actual row-norm marginal. -/
theorem weightedEnergy_product_le_marginal (U : Finset G) (V : Finset H)
    (w : G × H → ℝ) (k : H → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hk : ∀ v ∈ V, 0 ≤ k v)
    (hrows : ∀ v ∈ V, weightedEnergy U (fun a ↦ w (a,v)) ≤ M * k v ^ 4) :
    weightedEnergy (U ×ˢ V) w ≤ M * weightedEnergy V k := by
  rw [weightedEnergy_product_rows, weightedEnergy_eq_four_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro m hm
  split_ifs
  · have h := mixedWeightedEnergy_le_common_bound U
      (fun a ↦ w (a,i)) (fun a ↦ w (a,j)) (fun a ↦ w (a,l)) (fun a ↦ w (a,m))
      hM (hk i hi) (hk j hj) (hk l hl) (hk m hm)
      (hrows i hi) (hrows j hj) (hrows l hl) (hrows m hm)
    nlinarith
  · rw [mul_zero]

end
end Erdos539Geometry
