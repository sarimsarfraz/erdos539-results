/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Finite relative entropy, used only with the explicitly stated support
condition when the reference weight can vanish. -/
def finiteRelEntropy {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ x, p x * (Real.log (p x) - Real.log (q x))

/-- The finite log-sum inequality for arbitrary nonnegative weights.
It includes zero total mass and zero individual atoms. -/
theorem finite_log_sum {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hsupport : ∀ x, p x ≠ 0 → 0 < q x) :
    (∑ x, p x) * (Real.log (∑ x, p x) - Real.log (∑ x, q x)) ≤ finiteRelEntropy p q := by
  let P := ∑ x, p x
  let Q := ∑ x, q x
  have hPnonneg : 0 ≤ P := Finset.sum_nonneg (fun x _ ↦ hp x)
  by_cases hPzero : P = 0
  · have hpzero : ∀ x, p x = 0 := by
      intro x
      have hle : p x ≤ P := Finset.single_le_sum (fun y _ ↦ hp y) (Finset.mem_univ x)
      exact le_antisymm (hPzero ▸ hle) (hp x)
    simp [finiteRelEntropy, hpzero]
  have hP : 0 < P := lt_of_le_of_ne hPnonneg (Ne.symm hPzero)
  have hQ : 0 < Q := by
    have hQnonneg : 0 ≤ Q := Finset.sum_nonneg (fun x _ ↦ hq x)
    by_contra hQpos
    have hQzero : Q = 0 := le_antisymm (le_of_not_gt hQpos) hQnonneg
    have hpzero : ∀ x, p x = 0 := by
      intro x
      by_contra hx
      have hqx := hsupport x hx
      have hle : q x ≤ Q := Finset.single_le_sum (fun y _ ↦ hq y) (Finset.mem_univ x)
      linarith
    have : P = 0 := by simp [P, hpzero]
    exact hPzero this
  have hpoint : ∀ x, p x * (Real.log P - Real.log Q) + p x - q x * P / Q ≤
      p x * (Real.log (p x) - Real.log (q x)) := by
    intro x
    by_cases hx : p x = 0
    · simp only [hx, zero_mul, add_zero, zero_sub]
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg (hq x) hP.le) hQ.le)
    have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
    have hqx := hsupport x hx
    have ht := Real.log_le_sub_one_of_pos (div_pos (mul_pos hqx hP) (mul_pos hpx hQ))
    rw [Real.log_div (mul_ne_zero hqx.ne' hP.ne') (mul_ne_zero hx hQ.ne'),
      Real.log_mul hqx.ne' hP.ne', Real.log_mul hx hQ.ne'] at ht
    have hm := mul_le_mul_of_nonneg_left ht (hp x)
    have he : p x * (q x * P / (p x * Q)) = q x * P / Q := by field_simp
    simp only [mul_sub, mul_one, he] at hm
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ hpoint x)
  have hcancel : (∑ x, q x * P / Q) = P := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    change Q * P * Q⁻¹ = P
    field_simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hcancel] at hsum
  change P * (Real.log P - Real.log Q) + P - P ≤ finiteRelEntropy p q at hsum
  linarith

theorem finiteRelEntropy_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1)
    (hsupport : ∀ x, p x ≠ 0 → 0 < q x) : 0 ≤ finiteRelEntropy p q := by
  have h := finite_log_sum p q hp hq hsupport
  simpa only [hps, hqs, Real.log_one, sub_self, mul_zero] using h

end
end Erdos539Geometry
