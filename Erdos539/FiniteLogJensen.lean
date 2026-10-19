/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteGibbs

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

/-- Finite logarithmic Jensen inequality, including zero weights. -/
theorem finite_log_jensen {α : Type*} [Fintype α]
    (p x : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (hx : ∀ a, 0 < x a) :
    (∑ a, p a * Real.log (x a)) ≤ Real.log (∑ a, p a * x a) := by
  let M := ∑ a, p a * x a
  have hM : 0 < M := by
    obtain ⟨a, ha⟩ : ∃ a, 0 < p a := by
      by_contra h
      push_neg at h
      have hz : ∀ a, p a = 0 := fun a ↦ le_antisymm (h a) (hp a)
      simp [hz] at hs
    exact Finset.sum_pos' (fun a _ ↦ mul_nonneg (hp a) (hx a).le)
      ⟨a, Finset.mem_univ a, mul_pos ha (hx a)⟩
  have hpoint (a : α) :
      p a * Real.log (x a) ≤ p a * Real.log M + M⁻¹ * (p a * x a) - p a := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hx a) hM)
    rw [Real.log_div (hx a).ne' hM.ne'] at h
    have hm := mul_le_mul_of_nonneg_left h (hp a)
    simp only [div_eq_mul_inv] at hm
    nlinarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hpoint a)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hs, one_mul] at h
  change (∑ a, p a * Real.log (x a)) ≤ Real.log M + M⁻¹ * M - 1 at h
  simpa only [inv_mul_cancel₀ hM.ne', add_sub_cancel_right] using h

/-- Unweighted form, with the positive dimension made explicit. -/
theorem finite_sum_log_le {α : Type*} [Fintype α]
    (x : α → ℝ) (hx : ∀ a, 0 < x a) (hc : 0 < Fintype.card α) :
    (∑ a, Real.log (x a)) ≤ (Fintype.card α : ℝ) *
      Real.log ((∑ a, x a) / Fintype.card α) := by
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by
    change (0 : ℝ) < Fintype.card α
    exact_mod_cast hc
  have hs : ∑ _a : α, (1 / N : ℝ) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change N * (1 / N) = 1
    field_simp
  have h := finite_log_jensen (fun _ : α ↦ 1 / N) x (fun _ ↦ by positivity) hs hx
  simp only [← Finset.mul_sum, one_div] at h
  have hm := mul_le_mul_of_nonneg_left h hN.le
  rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at hm
  simpa only [div_eq_mul_inv, mul_comm] using hm

end
end Erdos539Geometry
