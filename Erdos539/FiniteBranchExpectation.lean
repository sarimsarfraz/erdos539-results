/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Exact expectation for an independent first branch and a second branch
whose finite outcome type depends on a sampled label. -/
theorem finite_branch_expectation {α β : Type*} {γ : β → Type*}
    [Fintype α] [Fintype β] [∀ y, Fintype (γ y)]
    (p : α → ℝ) (q : β → ℝ) (r : (y : β) → γ y → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) (hr : ∀ y, ∑ z, r y z = 1)
    (A : α → ℝ) (c : β → ℝ) (B : (y : β) → γ y → ℝ) :
    (∑ x : α × (Σ y, γ y), (p x.1 * (q x.2.1 * r x.2.1 x.2.2)) *
      (A x.1 + c x.2.1 + B x.2.1 x.2.2)) =
        (∑ a, p a * A a) + ∑ y, q y * (c y + ∑ b, r y b * B y b) := by
  have hrow (a : α) (y : β) : (∑ b, r y b * (A a + c y + B y b)) =
      A a + c y + ∑ b, r y b * B y b := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hr, one_mul]
  have hlabels (a : α) : (∑ y, q y * (A a + c y + ∑ b, r y b * B y b)) =
      A a + ∑ y, q y * (c y + ∑ b, r y b * B y b) := by
    simp only [add_assoc, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hq, one_mul]
  calc
    _ = ∑ a, p a * ∑ y, q y * ∑ b, r y b * (A a + c y + B y b) := by
      simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      simp_rw [hrow, hlabels]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]

theorem exists_le_positive_weighted_average {α : Type*} [Fintype α]
    (p f : α → ℝ) (hp : ∀ x, 0 < p x) (hs : ∑ x, p x = 1) :
    ∃ x, f x ≤ ∑ y, p y * f y := by
  have hne : (Finset.univ : Finset α).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at hs
    norm_num at hs
  have hsum : (∑ x, p x * f x) ≤ ∑ x, p x * (∑ y, p y * f y) := by
    rw [← Finset.sum_mul, hs, one_mul]
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨x, le_of_mul_le_mul_left hx (hp x)⟩

end
end Erdos539Geometry
