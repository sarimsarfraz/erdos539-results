/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

/-- Shannon entropy of a finite real-valued probability weight, in nats.
The definition also makes sense without the probability hypotheses. -/
def finiteEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (p x)

theorem finiteEntropy_ge_log_of_atom_bound {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    {L : ℝ} (_hL : 0 < L) (hb : ∀ x, p x ≤ 1 / L) :
    Real.log L ≤ finiteEntropy p := by
  have hpoint : ∀ x, p x * Real.log L ≤ Real.negMulLog (p x) := by
    intro x
    by_cases hx : p x = 0
    · simp [hx]
    · have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
      have hl := Real.log_le_log hpx (hb x)
      rw [one_div, Real.log_inv] at hl
      have hm := mul_le_mul_of_nonneg_left hl (hp x)
      dsimp [Real.negMulLog]
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ hpoint x)
  simpa only [← Finset.sum_mul, hs, one_mul, finiteEntropy] using hsum

/-- The usual finite-support entropy upper bound, proved directly with
log t <= t - 1. Zero atoms do not require removing the support. -/
theorem finiteEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    finiteEntropy p ≤ Real.log (Fintype.card α) := by
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hpoint : ∀ x, Real.negMulLog (p x) ≤ p x * Real.log N + 1 / N - p x := by
    intro x
    by_cases hx : p x = 0
    · simp only [hx, Real.negMulLog_zero, zero_mul, zero_add, sub_zero]
      positivity
    · have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
      have ht := Real.log_le_sub_one_of_pos (div_pos (one_pos) (mul_pos hN hpx))
      rw [one_div, Real.log_inv, Real.log_mul hN.ne' hx] at ht
      have hm := mul_le_mul_of_nonneg_left ht (hp x)
      have hid : p x * (N * p x)⁻¹ = 1 / N := by field_simp
      dsimp [Real.negMulLog]
      rw [mul_sub, hid] at hm
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ hpoint x)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    hs, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hNN : (Fintype.card α : ℝ) * (1 / N) = 1 := by change N * (1 / N) = 1; field_simp
  rw [hNN] at hsum
  simpa only [finiteEntropy, add_sub_cancel_right] using hsum

end
end Erdos539Geometry
