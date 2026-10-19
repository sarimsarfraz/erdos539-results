/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedGibbsLaw

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- The exact finite permutation square gap. -/
theorem finite_permutation_square_gap {α : Type*} [Fintype α]
    (e : α ≃ α) (u : α → ℝ) :
    (∑ a, u a ^ 2) - (∑ a, u a * u (e a)) =
      (1 / 2 : ℝ) * ∑ a, (u a - u (e a)) ^ 2 := by
  have he : (∑ a, u (e a) ^ 2) = ∑ a, u a ^ 2 := e.sum_comp (fun a ↦ u a ^ 2)
  have hexpand : (∑ a, (u a - u (e a)) ^ 2) =
      (∑ a, u a ^ 2) + (∑ a, u (e a) ^ 2) - 2 * ∑ a, u a * u (e a) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hexpand, he]
  ring

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def transferAmplitude (S : Finset G) (f g : S → ℝ) (t : (S × S) × (S × S)) : ℝ :=
  if t.1.1.val + t.1.2.val = t.2.1.val + t.2.2.val then
    f t.2.1 * f t.2.2 * Real.sqrt ((g t.1.1 * g t.1.2) / (g t.2.1 * g t.2.2)) else 0

def weightedTransferSum (S : Finset G) (f g : S → ℝ) : ℝ :=
  ∑ a : S, ∑ b : S, ∑ c : S, ∑ d : S,
    if a.val + b.val = c.val + d.val then
      (f c ^ 2 * f d ^ 2 * (g a * g b)) / (g c * g d) else 0

theorem transferAmplitude_square (S : Finset G) (f g : S → ℝ)
    (hg : ∀ a, 0 < g a) (t : (S × S) × (S × S)) :
    transferAmplitude S f g t ^ 2 =
      if t.1.1.val + t.1.2.val = t.2.1.val + t.2.2.val then
        (f t.2.1 ^ 2 * f t.2.2 ^ 2 * (g t.1.1 * g t.1.2)) / (g t.2.1 * g t.2.2) else 0 := by
  have ha := hg t.1.1
  have hb := hg t.1.2
  have hc := hg t.2.1
  have hd := hg t.2.2
  unfold transferAmplitude
  split_ifs
  · rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  · norm_num

theorem transferAmplitude_product (S : Finset G) (f g : S → ℝ)
    (hg : ∀ a, 0 < g a) (t : (S × S) × (S × S)) :
    transferAmplitude S f g t * transferAmplitude S f g t.swap =
      additiveQuadrupleWeight S f t.1.1 t.1.2 t.2.1 t.2.2 := by
  have ha := hg t.1.1
  have hb := hg t.1.2
  have hc := hg t.2.1
  have hd := hg t.2.2
  unfold transferAmplitude additiveQuadrupleWeight
  simp only [Prod.swap]
  by_cases ht : t.1.1.val + t.1.2.val = t.2.1.val + t.2.2.val
  · rw [if_pos ht, if_pos ht.symm, if_pos ht]
    have hpos : 0 ≤ (g t.1.1 * g t.1.2) / (g t.2.1 * g t.2.2) := by positivity
    have hroot : Real.sqrt ((g t.1.1 * g t.1.2) / (g t.2.1 * g t.2.2)) *
        Real.sqrt ((g t.2.1 * g t.2.2) / (g t.1.1 * g t.1.2)) = 1 := by
      rw [← Real.sqrt_mul hpos]
      have he : (g t.1.1 * g t.1.2) / (g t.2.1 * g t.2.2) *
          ((g t.2.1 * g t.2.2) / (g t.1.1 * g t.1.2)) = 1 := by
        field_simp [ha.ne', hb.ne', hc.ne', hd.ne']
      rw [he, Real.sqrt_one]
    calc
      _ = (f t.1.1 * f t.1.2 * (f t.2.1 * f t.2.2)) *
        (Real.sqrt ((g t.1.1 * g t.1.2) / (g t.2.1 * g t.2.2)) *
          Real.sqrt ((g t.2.1 * g t.2.2) / (g t.1.1 * g t.1.2))) := by ring
      _ = _ := by rw [hroot, mul_one]
  · simp [ht, Ne.symm ht]

/-- The first weighted inequality has exactly this sum-of-squares gap;
no optimizer or normalization assumption is used. -/
theorem weightedTransferSum_gap (S : Finset G) (f g : S → ℝ) (hg : ∀ a, 0 < g a) :
    weightedTransferSum S f g - weightedGibbsPartition S f =
      (1 / 2 : ℝ) * ∑ t : (S × S) × (S × S),
        (transferAmplitude S f g t - transferAmplitude S f g t.swap) ^ 2 := by
  have h := finite_permutation_square_gap (Equiv.prodComm (S × S) (S × S)) (transferAmplitude S f g)
  simp only [Equiv.prodComm_apply, transferAmplitude_square S f g hg,
    transferAmplitude_product S f g hg] at h
  simpa only [Fintype.sum_prod_type, weightedTransferSum, weightedGibbsPartition_eq_sum] using h

theorem weightedEnergy_le_transfer (S : Finset G) (f g : S → ℝ) (hg : ∀ a, 0 < g a) :
    weightedGibbsPartition S f ≤ weightedTransferSum S f g := by
  have h := weightedTransferSum_gap S f g hg
  have hn : 0 ≤ (1 / 2 : ℝ) * ∑ t : (S × S) × (S × S),
      (transferAmplitude S f g t - transferAmplitude S f g t.swap) ^ 2 := by positivity
  linarith

end
end Erdos539Geometry
