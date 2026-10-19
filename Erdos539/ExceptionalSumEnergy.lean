/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyNormBasics
import Erdos539.EnergyRestriction

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sum_sq_le_of_injective_map {α β : Type*} [DecidableEq β]
    (U : Finset α) (V : Finset β) (g : α → β) (f : β → ℝ)
    (hmap : ∀ x ∈ U, g x ∈ V) (hinj : Set.InjOn g U) :
    (∑ x ∈ U, f (g x) ^ 2) ≤ ∑ y ∈ V, f y ^ 2 := by
  classical
  calc
    _ = ∑ y ∈ U.image g, f y ^ 2 := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro y hy; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact hmap x hx)
      (fun y _ _ ↦ sq_nonneg (f y))

/-- Any single convolution coefficient is bounded by the square mass.
No nonnegativity of the weight or reflection invariance is needed. -/
theorem weightedConvolution_sq_le_squareSum_sq (S : Finset G) (f : G → ℝ) (z : G) :
    weightedConvolution S f f z ^ 2 ≤ weightSquareSum S f ^ 2 := by
  let U := fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z
  have hf : (∑ p ∈ U, f p.1 ^ 2) ≤ weightSquareSum S f := by
    apply sum_sq_le_of_injective_map U S Prod.fst f
    · intro p hp
      exact (Finset.mem_product.mp (mem_fiber.mp hp).1).1
    · intro p hp q hq he
      have hs := (mem_fiber.mp hp).2.trans (mem_fiber.mp hq).2.symm
      rw [he] at hs
      exact Prod.ext he (add_left_cancel hs)
  have hg : (∑ p ∈ U, f p.2 ^ 2) ≤ weightSquareSum S f := by
    apply sum_sq_le_of_injective_map U S Prod.snd f
    · intro p hp
      exact (Finset.mem_product.mp (mem_fiber.mp hp).1).2
    · intro p hp q hq he
      have hs := (mem_fiber.mp hp).2.trans (mem_fiber.mp hq).2.symm
      rw [he] at hs
      exact Prod.ext (add_right_cancel hs) he
  have h := Finset.sum_mul_sq_le_sq_mul_sq U (fun p ↦ f p.1) (fun p ↦ f p.2)
  exact h.trans (by
    rw [pow_two]
    exact mul_le_mul hf hg (Finset.sum_nonneg (fun p _ ↦ sq_nonneg (f p.2))) (weightSquareSum_nonneg S f))

/-- If every sum except one has at most R ordered representations, the
entire energy is at most (R+1) times the squared square mass. -/
theorem weightedEnergy_le_exceptional_sum_bound (S : Finset G) (w : G) {R : ℝ}
    (hR : 0 ≤ R)
    (hrepr : ∀ z : G, z ≠ w → ((fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z).card : ℝ) ≤ R)
    (f : G → ℝ) : weightedEnergy S f ≤ (R + 1) * weightSquareSum S f ^ 2 := by
  have hpoint : ∀ z : G, weightedConvolution S f f z ^ 2 ≤
      R * (∑ p ∈ fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z, (f p.1 * f p.2) ^ 2) +
        if z = w then weightSquareSum S f ^ 2 else 0 := by
    intro z
    by_cases hz : z = w
    · rw [if_pos hz]
      have h := weightedConvolution_sq_le_squareSum_sq S f z
      have hn : 0 ≤ R * (∑ p ∈ fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z, (f p.1 * f p.2) ^ 2) :=
        mul_nonneg hR (Finset.sum_nonneg (fun p _ ↦ sq_nonneg _))
      linarith
    · rw [if_neg hz, add_zero]
      have h := Finset.sum_mul_sq_le_sq_mul_sq
        (fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z) (fun _ ↦ (1 : ℝ)) (fun p ↦ f p.1 * f p.2)
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hrepr z hz) (Finset.sum_nonneg (fun p _ ↦ sq_nonneg _)))
  have hsum := Finset.sum_le_sum (s := S + S) (fun z _ ↦ hpoint z)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_weighted_fibers] at hsum
  have hpairs : (∑ p ∈ S ×ˢ S, (f p.1 * f p.2) ^ 2) = weightSquareSum S f ^ 2 := by
    simp_rw [mul_pow]
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp only [weightSquareSum, pow_two]
  rw [hpairs] at hsum
  have hsingle : (∑ z ∈ S + S, if z = w then weightSquareSum S f ^ 2 else 0) ≤ weightSquareSum S f ^ 2 := by
    simp only [Finset.sum_ite_eq']
    split_ifs
    · rfl
    · exact sq_nonneg _
  change weightedEnergy S f ≤ _ at hsum
  nlinarith

theorem energyNorm_le_exceptional_sum_bound (S : Finset G) (w : G) {R : ℝ}
    (hR : 0 ≤ R)
    (hrepr : ∀ z : G, z ≠ w → ((fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z).card : ℝ) ≤ R) :
    energyNorm S ≤ R + 1 := by
  by_cases hS : S.Nonempty
  · obtain ⟨f, _, hf, hE⟩ := energyNorm_attained hS
    have h := weightedEnergy_le_exceptional_sum_bound S w hR hrepr (extendWeight S f)
    simpa only [hE, weightSquareSum_extend, hf, one_pow, mul_one] using h
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, energyNorm_empty]
    linarith

end
end Erdos539Geometry
