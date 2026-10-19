/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteGibbs

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- Positive reference weights with arbitrarily small log partition and
cross entropy no larger than the original entropy. This handles zero atoms
without deleting any points from the ambient support. -/
theorem finite_positive_reference {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : α → ℝ, (∀ a, 0 < w a) ∧ Real.log (∑ a, w a) ≤ ε ∧
      -(∑ a, ν a * Real.log (w a)) ≤ finiteEntropy ν := by
  let n : ℝ := Fintype.card α
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let δ := ε / (n + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let w : α → ℝ := fun a ↦ ν a + δ
  have hw : ∀ a, 0 < w a := fun a ↦ add_pos_of_nonneg_of_pos (hν a) hδ
  have hsum : (∑ a, w a) = 1 + n * δ := by
    simp only [w, Finset.sum_add_distrib, hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n]
  have hspos : 0 < ∑ a, w a := by rw [hsum]; positivity
  refine ⟨w, hw, ?_, ?_⟩
  · have hlog := Real.log_le_sub_one_of_pos hspos
    have hsmall : n * δ ≤ ε := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by linarith : 0 < n + 1)).mpr
      nlinarith
    rw [hsum] at hlog ⊢
    linarith
  · simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    apply neg_le_neg
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : ν a = 0
    · simp [ha]
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (lt_of_le_of_ne (hν a) (Ne.symm ha)) (by dsimp [w]; linarith)) (hν a)

end
end Erdos539Geometry
