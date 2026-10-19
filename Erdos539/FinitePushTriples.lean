/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FinitePushProducts

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem finitePush_first3 {α : Type*} [Fintype α] (p : (α × α) × α → ℝ) (a : α) :
    finitePush p (fun z ↦ z.1.1) a = ∑ b, ∑ c, p ((a, b), c) := by
  simp only [finitePush, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem finitePush_second3 {α : Type*} [Fintype α] (p : (α × α) × α → ℝ) (b : α) :
    finitePush p (fun z ↦ z.1.2) b = ∑ a, ∑ c, p ((a, b), c) := by
  simp only [finitePush, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem finitePush_third3 {α : Type*} [Fintype α] (p : (α × α) × α → ℝ) (c : α) :
    finitePush p Prod.snd c = ∑ a, ∑ b, p ((a, b), c) := by
  rw [finitePush_snd]
  exact Fintype.sum_prod_type _

def mapThree {α β : Type*} (e : α → β) : (α × α) × α → (β × β) × β :=
  fun z ↦ ((e z.1.1, e z.1.2), e z.2)

def independentTriple {α : Type*} (ν : α → ℝ) : (α × α) × α → ℝ :=
  fun z ↦ ν z.1.1 * ν z.1.2 * ν z.2

/-- Pushing all three independent coordinates preserves the product
reference law. This is the exact reference needed for data processing. -/
theorem finitePush_independentTriple {α β : Type*} [Fintype α]
    (ν : α → ℝ) (e : α → β) :
    finitePush (independentTriple ν) (mapThree e) = independentTriple (finitePush ν e) := by
  funext z
  rcases z with ⟨⟨a, b⟩, c⟩
  simp only [finitePush, independentTriple, mapThree, Fintype.sum_prod_type,
    Prod.mk.injEq]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : e x = a <;> by_cases hy : e y = b <;> by_cases hz : e z = c <;> simp [hx, hy, hz]

end
end Erdos539Geometry
