/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductEnergy
import Erdos539.RationalSidonSums

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Additive sums determine the unordered pair, including diagonal pairs. -/
def HasSidonSums (S : Finset G) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem sidon_quadruple_term {S : Finset G} (hS : HasSidonSums S)
    (w : G → ℝ) {a b c d : G} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    (if a + b = c + d then (w a * w b) * (w c * w d) else 0) =
      (if c = a ∧ d = b then w a ^ 2 * w b ^ 2 else 0) +
      (if c = b ∧ d = a then w a ^ 2 * w b ^ 2 else 0) -
      (if a = b ∧ c = a ∧ d = a then w a ^ 4 else 0) := by
  have he : a + b = c + d ↔ (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
    constructor
    · intro h
      rcases hS a ha b hb c hc d hd h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁.symm, h₂.symm⟩
      · exact Or.inr ⟨h₂.symm, h₁.symm⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact add_comm _ _
  simp only [he]
  by_cases hca : c = a
  · subst c
    by_cases hdb : d = b
    · subst d
      by_cases hab : a = b
      · subst b; simp; ring
      · simp [hab, Ne.symm hab]; ring
    · by_cases hab : a = b
      · subst b; simp [hdb]
      · simp [hab, hdb]
  · by_cases hcb : c = b
    · subst c
      by_cases hda : d = a
      · subst d; simp [hca, Ne.symm hca]; ring
      · simp [hca, hda]
    · simp [hca, hcb]

/-- Exact energy of a Sidon support, with arbitrary real weights. -/
theorem weightedEnergy_sidon {S : Finset G} (hS : HasSidonSums S) (w : G → ℝ) :
    weightedEnergy S w = 2 * (∑ a ∈ S, w a ^ 2) ^ 2 - ∑ a ∈ S, w a ^ 4 := by
  rw [weightedEnergy_eq_four_sum]
  calc
    _ = ∑ a ∈ S, ∑ b ∈ S,
        (2 * (w a ^ 2 * w b ^ 2) - if a = b then w a ^ 4 else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      calc
        _ = ∑ c ∈ S, ∑ d ∈ S,
            ((if c = a ∧ d = b then w a ^ 2 * w b ^ 2 else 0) +
             (if c = b ∧ d = a then w a ^ 2 * w b ^ 2 else 0) -
             (if a = b ∧ c = a ∧ d = a then w a ^ 4 else 0)) := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          exact sidon_quadruple_term hS w ha hb hc hd
        _ = _ := by
          simp only [ite_and]
          by_cases hab : a = b
          · subst b; simp [ha, Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring
          · simp [hab, ha, hb, Finset.sum_add_distrib]; ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      simp
      ring

/-- The integer certificate yields the rational Sidon energy inequality
for the literal convolution energy, with no unproved analytic input. -/
theorem weightedEnergy_sidon_rational_bound {S : Finset G} (hS : HasSidonSums S)
    (w : G → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    weightedEnergy S w ≤ (∑ i ∈ S, w i ^ (20 / 13 : ℝ)) ^ (13 / 5 : ℝ) := by
  rw [weightedEnergy_sidon hS]
  exact rational_sidon_energy_bound S w hw

end
end Erdos539Geometry
