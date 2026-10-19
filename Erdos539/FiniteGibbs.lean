/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

/-- The finite Gibbs entropy inequality, with zero reference weights
allowed wherever the probability weight also vanishes. -/
theorem finiteEntropy_le_log_partition {α : Type*} [Fintype α]
    (p w : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (hw : ∀ x, 0 ≤ w x) (hW : 0 < ∑ x, w x)
    (hsupport : ∀ x, p x ≠ 0 → 0 < w x) :
    finiteEntropy p ≤ Real.log (∑ x, w x) - ∑ x, p x * Real.log (w x) := by
  let W := ∑ x, w x
  have hpoint : ∀ x, Real.negMulLog (p x) ≤
      p x * Real.log W - p x * Real.log (w x) + w x / W - p x := by
    intro x
    by_cases hx : p x = 0
    · simp only [hx, Real.negMulLog_zero, zero_mul, sub_self, zero_add, sub_zero]
      exact div_nonneg (hw x) hW.le
    have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
    have hwx := hsupport x hx
    have ht := Real.log_le_sub_one_of_pos (div_pos hwx (mul_pos hW hpx))
    rw [Real.log_div hwx.ne' (mul_ne_zero hW.ne' hx), Real.log_mul hW.ne' hx] at ht
    change Real.log (w x) - (Real.log W + Real.log (p x)) ≤ w x / (W * p x) - 1 at ht
    have hm := mul_le_mul_of_nonneg_left ht (hp x)
    have hid : p x * (w x / (W * p x)) = w x / W := by field_simp
    simp only [mul_sub, mul_one, hid] at hm
    dsimp [Real.negMulLog]
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ hpoint x)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    div_eq_mul_inv, hs, one_mul] at hsum
  have he : (∑ x, w x) * W⁻¹ = 1 := mul_inv_cancel₀ hW.ne'
  rw [he, add_sub_cancel_right] at hsum
  exact hsum

/-- Nonnegativity of relative entropy, in finite real-valued notation. -/
theorem finiteEntropy_le_crossEntropy {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (hq : ∀ x, 0 ≤ q x) (hqs : ∑ x, q x = 1)
    (hsupport : ∀ x, p x ≠ 0 → 0 < q x) :
    finiteEntropy p ≤ -∑ x, p x * Real.log (q x) := by
  have h := finiteEntropy_le_log_partition p q hp hs hq (by rw [hqs]; norm_num) hsupport
  simpa only [hqs, Real.log_one, zero_sub] using h

/-- Entropy is nonnegative for a finite probability weight. -/
theorem finiteEntropy_nonneg {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    0 ≤ finiteEntropy p := by
  apply Finset.sum_nonneg
  intro x _
  have hx : p x ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun y _ ↦ hp y) (Finset.mem_univ x)
  exact Real.negMulLog_nonneg (hp x) hx

end
end Erdos539Geometry
