/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem finitePush_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (a : α) : finitePush p Prod.fst a = ∑ b, p (a, b) := by
  simp only [finitePush, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem finitePush_snd {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (b : β) : finitePush p Prod.snd b = ∑ a, p (a, b) := by
  simp [finitePush, Fintype.sum_prod_type]

theorem finitePush_eq_zero_of_fiber_zero {α β : Type*} [Fintype α]
    (p : α → ℝ) (f : α → β) (b : β) (h : ∀ a, f a = b → p a = 0) :
    finitePush p f b = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with ha
  · exact h a ha
  · rfl

theorem finitePush_id {α : Type*} [Fintype α] (p : α → ℝ) : finitePush p id = p := by
  funext a
  unfold finitePush
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem finitePush_first4 {α : Type*} [Fintype α]
    (p : (α × α) × (α × α) → ℝ) (a : α) :
    finitePush p (fun z ↦ z.1.1) a = ∑ b, ∑ c, ∑ d, p ((a, b), (c, d)) := by
  simp only [finitePush, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem finitePush_second4 {α : Type*} [Fintype α]
    (p : (α × α) × (α × α) → ℝ) (b : α) :
    finitePush p (fun z ↦ z.1.2) b = ∑ a, ∑ c, ∑ d, p ((a, b), (c, d)) := by
  simp only [finitePush, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem finitePush_third4 {α : Type*} [Fintype α]
    (p : (α × α) × (α × α) → ℝ) (c : α) :
    finitePush p (fun z ↦ z.2.1) c = ∑ a, ∑ b, ∑ d, p ((a, b), (c, d)) := by
  simp only [finitePush, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single c]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem finitePush_fourth4 {α : Type*} [Fintype α]
    (p : (α × α) × (α × α) → ℝ) (d : α) :
    finitePush p (fun z ↦ z.2.2) d = ∑ a, ∑ b, ∑ c, p ((a, b), (c, d)) := by
  simp [finitePush, Fintype.sum_prod_type]

end
end Erdos539Geometry
