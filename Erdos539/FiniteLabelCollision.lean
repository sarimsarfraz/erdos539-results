/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- The squared masses of label classes count exactly equal-label pairs. -/
theorem finitePush_square_collision {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (label : α → β) :
    (∑ b, finitePush w label b ^ 2) =
      ∑ a, ∑ a', if label a' = label a then w a * w a' else 0 := by
  simp only [pow_two]
  rw [finitePush_expectation]
  simp only [finitePush, Finset.mul_sum, mul_ite, mul_zero]

/-- A d-label partition forces at least mass^2/d equal-label pair weight. -/
theorem finite_label_collision_bound {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (w : α → ℝ) (label : α → β) :
    (∑ a, w a) ^ 2 / (Fintype.card β : ℝ) ≤
      ∑ a, ∑ a', if label a' = label a then w a * w a' else 0 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset β)
    (fun _ ↦ (1 : ℝ)) (finitePush w label)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    finitePush_sum] at h
  rw [finitePush_square_collision] at h
  exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card β)).mpr (by simpa only [mul_comm] using h)

end
end Erdos539Geometry
