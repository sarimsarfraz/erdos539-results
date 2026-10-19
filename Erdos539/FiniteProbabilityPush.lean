/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteGibbs

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Literal pushforward of a finite real-valued weight. -/
def finitePush {α β : Type*} [Fintype α] (p : α → ℝ) (f : α → β) (b : β) : ℝ :=
  ∑ a, if f a = b then p a else 0

theorem finitePush_nonneg {α β : Type*} [Fintype α]
    (p : α → ℝ) (f : α → β) (hp : ∀ a, 0 ≤ p a) (b : β) :
    0 ≤ finitePush p f b := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · rfl

theorem finitePush_expectation {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → ℝ) :
    (∑ b, finitePush p f b * g b) = ∑ a, p a * g (f a) := by
  simp only [finitePush, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem finitePush_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) : (∑ b, finitePush p f b) = ∑ a, p a := by
  simpa only [mul_one] using finitePush_expectation p f (fun _ ↦ 1)

theorem finitePush_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → γ) :
    finitePush (finitePush p f) g = finitePush p (g ∘ f) := by
  funext c
  have h := finitePush_expectation p f (fun b ↦ if g b = c then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, finitePush, Function.comp_apply] using h

theorem le_finitePush {α β : Type*} [Fintype α]
    (p : α → ℝ) (f : α → β) (hp : ∀ a, 0 ≤ p a) (a : α) :
    p a ≤ finitePush p f (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun x ↦ if f x = f a then p x else 0)
    (fun x _ ↦ by dsimp only; split_ifs; exact hp x; rfl) (Finset.mem_univ a)
  simpa only [if_pos rfl, finitePush] using h

/-- Entropy cannot increase under a deterministic map. This version
even permits unnormalized nonnegative weights. -/
theorem finiteEntropy_push_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (hp : ∀ a, 0 ≤ p a) :
    finiteEntropy (finitePush p f) ≤ finiteEntropy p := by
  have he := finitePush_expectation p f (fun b ↦ -Real.log (finitePush p f b))
  have hpoint : ∀ a, p a * (-Real.log (finitePush p f (f a))) ≤ Real.negMulLog (p a) := by
    intro a
    by_cases ha : p a = 0
    · simp [ha]
    have hpa : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm ha)
    have hl := Real.log_le_log hpa (le_finitePush p f hp a)
    have hm := mul_le_mul_of_nonneg_left hl (hp a)
    dsimp [Real.negMulLog]
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hpoint a)
  have hleft : finiteEntropy (finitePush p f) = ∑ a, p a * (-Real.log (finitePush p f (f a))) := by
    simpa only [finiteEntropy, Real.negMulLog, mul_neg, neg_mul] using he
  rw [hleft]
  exact hsum

end
end Erdos539Geometry
