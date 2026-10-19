/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GeneralPowerInterpolation
import Mathlib.Logic.Equiv.Fin.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- A power-sized family with simultaneous positive- and ordinary-difference
control. The constant is uniform in the integral scale parameter. -/
def HasPowerConstruction (d a b : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ W : ℕ, ∃ F : Finset (Fin d → ℤ),
    F.card = W ^ a ∧ (integerPositiveDifferences F).card ≤ C * W ^ b ∧
      (integerDifferences F).card ≤ C * W ^ a

theorem hasPowerConstruction_one : HasPowerConstruction 1 1 1 := by
  classical
  refine ⟨2, by decide, ?_⟩
  intro W
  let e : Unit ≃ Fin 1 := Fintype.equivOfCardEq (by simp)
  refine ⟨(intervalVectors W).image (reindexInteger e), ?_, ?_, ?_⟩
  · rw [reindexInteger_card, intervalVectors_card, pow_one]
  · rw [integerPositiveDifferences_reindex_card, pow_one]
    exact (intervalVectors_posDiff_card_le W).trans (by omega)
  · rw [integerDifferences_reindex_card, pow_one]
    exact intervalVectors_differences_card_le W

/-- Gluing preserves the uniform linear ordinary-difference estimate and
combines the positive-difference exponents additively. -/
theorem HasPowerConstruction.glue {p s a₁ b₁ a₂ b₂ : ℕ} (hp : 0 < p)
    (h₁ : HasPowerConstruction p a₁ b₁) (h₂ : HasPowerConstruction s a₂ b₂)
    (hbalance : a₁ * a₂ ≤ b₁ * a₂ + b₂ * a₁) :
    HasPowerConstruction (p + s) (a₁ * a₂ + (b₁ * a₂ + b₂ * a₁)) (b₁ * a₂ + b₂ * a₁) := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := h₁
  obtain ⟨C₂, hC₂, h₂⟩ := h₂
  let A := a₁ * a₂
  let B := b₁ * a₂ + b₂ * a₁
  let C := 2 * C₁ * C₂ + C₁ + C₂
  have hAB : A ≤ B := hbalance
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro W
  obtain ⟨F, hF, hDF, hΔF⟩ := h₁ (W ^ a₂)
  obtain ⟨G, hG, hDG, hΔG⟩ := h₂ (W ^ a₁)
  have hpowA : (W ^ a₂) ^ a₁ = W ^ A := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have hpowA' : (W ^ a₁) ^ a₂ = W ^ A := (pow_mul _ _ _).symm
  rw [hpowA] at hF hΔF
  rw [hpowA'] at hG hΔG
  let K := W ^ (B - A)
  have hKA : K * W ^ A = W ^ B := by dsimp only [K]; rw [← pow_add, Nat.sub_add_cancel hAB]
  have hKAA : K * W ^ A * W ^ A = W ^ (A + B) := by
    rw [hKA, ← pow_add, Nat.add_comm B A]
  have hprodB : (W ^ a₂) ^ b₁ * (W ^ a₁) ^ b₂ = W ^ B := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    dsimp only [B]
    ring
  obtain ⟨H, hH, hDH, hΔH⟩ := exists_gluing F G K ⟨0, hp⟩
  let e : Fin p ⊕ Fin s ≃ Fin (p + s) := finSumFinEquiv
  refine ⟨H.image (reindexInteger e), ?_, ?_, ?_⟩
  · rw [reindexInteger_card, hH, hF, hG]
    exact hKAA
  · rw [integerPositiveDifferences_reindex_card]
    have hpos : (integerPositiveDifferences H).card ≤ (C₁ * C₂ + C₁ + C₂) * W ^ B := by
      calc
        _ ≤ _ := hDH
        _ ≤ (C₁ * (W ^ a₂) ^ b₁) * (C₂ * (W ^ a₁) ^ b₂) +
            K * (C₁ * W ^ A + C₂ * W ^ A) :=
          Nat.add_le_add (Nat.mul_le_mul hDF hDG)
            (Nat.mul_le_mul (Nat.sub_le K 1) (Nat.add_le_add hΔF hΔG))
        _ = (C₁ * C₂) * ((W ^ a₂) ^ b₁ * (W ^ a₁) ^ b₂) +
            (C₁ + C₂) * (K * W ^ A) := by ring
        _ = _ := by rw [hprodB, hKA]; ring
    exact hpos.trans (Nat.mul_le_mul_right _ (by dsimp only [C]; nlinarith))
  · rw [integerDifferences_reindex_card]
    have hdiff : (integerDifferences H).card ≤ (2 * C₁ * C₂) * W ^ (A + B) := by
      calc
        _ ≤ _ := hΔH
        _ ≤ (2 * K) * (C₁ * W ^ A) * (C₂ * W ^ A) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le (2 * K) 1) hΔF) hΔG
        _ = (2 * C₁ * C₂) * (K * W ^ A * W ^ A) := by ring
        _ = _ := by rw [hKAA]
    exact hdiff.trans (Nat.mul_le_mul_right _ (by dsimp only [C]; omega))

end
end Erdos539Geometry
