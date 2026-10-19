/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PairCounting
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def weightSquareSum (S : Finset G) (f : G → ℝ) : ℝ := ∑ x ∈ S, f x ^ 2

def weightedConvolution (S : Finset G) (f g : G → ℝ) (z : G) : ℝ :=
  ∑ p ∈ fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z, f p.1 * g p.2

/-- The actual additive energy is the squared L2 norm of convolution.
All sums use the supplied finite support; no spectral or entropy premise
is built into this definition. -/
def weightedEnergy (S : Finset G) (f : G → ℝ) : ℝ :=
  ∑ z ∈ S + S, weightedConvolution S f f z ^ 2

omit [AddCommGroup G] [DecidableEq G] in
theorem weightSquareSum_nonneg (S : Finset G) (f : G → ℝ) : 0 ≤ weightSquareSum S f :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem weightedEnergy_nonneg (S : Finset G) (f : G → ℝ) : 0 ≤ weightedEnergy S f :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

omit [DecidableEq G] in
theorem weightedConvolution_nonneg {S : Finset G} {f g : G → ℝ}
    (hf : ∀ x ∈ S, 0 ≤ f x) (hg : ∀ x ∈ S, 0 ≤ g x) (z : G) :
    0 ≤ weightedConvolution S f g z := by
  apply Finset.sum_nonneg
  intro p hp
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp (mem_fiber.mp hp).1
  exact mul_nonneg (hf _ hx) (hg _ hy)

omit [DecidableEq G] in
theorem weightedConvolution_scale (S : Finset G) (f g : G → ℝ) (a b : ℝ) (z : G) :
    weightedConvolution S (fun x ↦ a * f x) (fun x ↦ b * g x) z =
      a * b * weightedConvolution S f g z := by
  unfold weightedConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem weightedEnergy_scale (S : Finset G) (f : G → ℝ) (c : ℝ) :
    weightedEnergy S (fun x ↦ c * f x) = c ^ 4 * weightedEnergy S f := by
  unfold weightedEnergy
  simp_rw [weightedConvolution_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

omit [DecidableEq G] in
theorem sum_fiber_card_le (S : Finset G) (z : G) :
    (fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (mem_fiber.mp hp).1).1
  · intro p hp q hq he
    apply Prod.ext he
    have hp' := (mem_fiber.mp hp).2
    have hq' := (mem_fiber.mp hq).2
    rw [he] at hp'
    exact add_left_cancel (hp'.trans hq'.symm)

omit [DecidableEq G] in
theorem weightedConvolution_sq_le (S : Finset G) (f g : G → ℝ) (z : G) :
    weightedConvolution S f g z ^ 2 ≤
      S.card * ∑ p ∈ fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z, (f p.1 * g p.2) ^ 2 := by
  let R := fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z
  have h := Finset.sum_mul_sq_le_sq_mul_sq R (fun _ ↦ (1 : ℝ)) (fun p ↦ f p.1 * g p.2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hcard : (R.card : ℝ) ≤ S.card := by exact_mod_cast sum_fiber_card_le S z
  exact h.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

theorem sum_weighted_fibers (S : Finset G) (w : G × G → ℝ) :
    ∑ z ∈ S + S, ∑ p ∈ fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z, w p =
      ∑ p ∈ S ×ˢ S, w p := by
  refine @Finset.sum_fiberwise_of_maps_to (G × G) G ℝ _ (S ×ˢ S) (S + S)
    (Classical.decEq G) (fun p ↦ p.1 + p.2) ?_ w
  intro p hp
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  exact Finset.mem_add.mpr ⟨p.1, hx, p.2, hy, rfl⟩

/-- The universal upper bound, before normalization. -/
theorem weightedEnergy_le_card_mul_squareSum_sq (S : Finset G) (f : G → ℝ) :
    weightedEnergy S f ≤ S.card * weightSquareSum S f ^ 2 := by
  calc
    _ ≤ ∑ z ∈ S + S, (S.card : ℝ) *
        ∑ p ∈ fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z, (f p.1 * f p.2) ^ 2 :=
      Finset.sum_le_sum (fun z _ ↦ weightedConvolution_sq_le S f f z)
    _ = S.card * ∑ p ∈ S ×ˢ S, (f p.1 * f p.2) ^ 2 := by
      rw [← Finset.mul_sum, sum_weighted_fibers]
    _ = _ := by
      simp_rw [mul_pow]
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      simp only [weightSquareSum, pow_two]

end
end Erdos539Geometry
