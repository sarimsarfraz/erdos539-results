/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Entropy of a finite law assembled from normalized conditional rows.
No positivity hypothesis is needed for this algebraic identity. -/
theorem finiteEntropy_rows {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (k : α → β → ℝ) (hk : ∀ a, ∑ b, k a b = 1) :
    finiteEntropy (fun z : α × β ↦ ν z.1 * k z.1 z.2) =
      finiteEntropy ν + ∑ a, ν a * finiteEntropy (k a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, Real.negMulLog_mul]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hk, one_mul]

/-- A normalized finite reference law attains its Gibbs bound, including
zero reference weights. -/
theorem finiteEntropy_normalize {α : Type*} [Fintype α]
    (w : α → ℝ) (hW : 0 < ∑ a, w a) :
    finiteEntropy (fun a ↦ w a / ∑ b, w b) =
      Real.log (∑ b, w b) - ∑ a, (w a / ∑ b, w b) * Real.log (w a) := by
  let W := ∑ b, w b
  have hsum : ∑ a, w a / W = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hW.ne'
  have hpoint (a : α) : Real.negMulLog (w a / W) =
      (w a / W) * Real.log W - (w a / W) * Real.log (w a) := by
    by_cases hw : w a = 0
    · simp [hw]
    · rw [Real.negMulLog, Real.log_div hw hW.ne']
      ring
  change (∑ a, Real.negMulLog (w a / W)) = Real.log W - _
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]

/-- Pushforward only depends on the map on the nonzero support. -/
theorem finitePush_congr_on_support {α β : Type*} [Fintype α]
    (p : α → ℝ) (e f : α → β) (h : ∀ a, p a ≠ 0 → e a = f a) :
    finitePush p e = finitePush p f := by
  funext b
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

end
end Erdos539Geometry
