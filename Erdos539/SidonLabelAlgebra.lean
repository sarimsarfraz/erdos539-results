/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RationalSidonSums

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Equality of unordered pairs with multiplicity, including diagonals. -/
def SameUnorderedPair {ι : Type*} (a b c d : ι) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem unordered_pair_weight_term {ι : Type*} (w : ι → ℝ) (a b c d : ι) :
    (if SameUnorderedPair a b c d then (w a * w b) * (w c * w d) else 0) =
      (if c = a ∧ d = b then w a ^ 2 * w b ^ 2 else 0) +
      (if c = b ∧ d = a then w a ^ 2 * w b ^ 2 else 0) -
      (if a = b ∧ c = a ∧ d = a then w a ^ 4 else 0) := by
  unfold SameUnorderedPair
  by_cases hca : c = a
  · subst c
    by_cases hdb : d = b
    · subst d
      by_cases hab : a = b
      · subst b; simp; ring
      · simp [hab, Ne.symm hab]; ring
    · by_cases hab : a = b
      · subst b; simp [hdb, Ne.symm hdb]
      · simp [hab, Ne.symm hab, hdb, Ne.symm hdb]
  · by_cases hcb : c = b
    · subst c
      by_cases hda : d = a
      · subst d; simp [hca, Ne.symm hca]; ring
      · simp [hca, Ne.symm hca, hda, Ne.symm hda]
    · simp [hca, Ne.symm hca, hcb, Ne.symm hcb]

theorem unordered_pair_energy {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      if SameUnorderedPair a b c d then (w a * w b) * (w c * w d) else 0) =
      2 * (∑ a, w a ^ 2) ^ 2 - ∑ a, w a ^ 4 := by
  calc
    _ = ∑ a, ∑ b, (2 * (w a ^ 2 * w b ^ 2) - if a = b then w a ^ 4 else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp_rw [unordered_pair_weight_term]
      simp only [ite_and]
      by_cases hab : a = b
      · subst b; simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring
      · simp [hab, Finset.sum_add_distrib]; ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      simp
      ring

end
end Erdos539Geometry
