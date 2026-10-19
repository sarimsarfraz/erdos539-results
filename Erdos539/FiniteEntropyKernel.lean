/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteDataProcessing

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem finiteEntropy_push_expectation {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) :
    finiteEntropy (finitePush p f) = ∑ a, p a * (-Real.log (finitePush p f (f a))) := by
  have h := finitePush_expectation p f (fun b ↦ -Real.log (finitePush p f b))
  simpa only [finiteEntropy, Real.negMulLog, mul_neg, neg_mul] using h

/-- Observations determining exactly the same input fibers have exactly
the same output entropy under every input law. -/
theorem finiteEntropy_push_eq_of_same_fibers {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (p : α → ℝ) (f : α → β) (g : α → γ)
    (h : ∀ a b, f a = f b ↔ g a = g b) :
    finiteEntropy (finitePush p f) = finiteEntropy (finitePush p g) := by
  rw [finiteEntropy_push_expectation, finiteEntropy_push_expectation]
  apply Finset.sum_congr rfl
  intro a _
  have he : finitePush p f (f a) = finitePush p g (g a) := by
    simp only [finitePush, h]
  rw [he]

end
end Erdos539Geometry
