/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PowerConstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- Rounding up an eighth root loses at most a factor 32 in the fifth power. -/
theorem exists_eighth_power_size {n : ℕ} (hn : 0 < n) :
    ∃ W : ℕ, n ≤ W ^ 8 ∧ (W : ℝ) ^ 5 ≤ 32 * (n : ℝ) ^ (5 / 8 : ℝ) := by
  let r : ℝ := (n : ℝ) ^ (1 / 8 : ℝ)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : 1 ≤ r := Real.one_le_rpow hn1 (by norm_num)
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr1
  let W := Nat.ceil r
  have hrW : r ≤ (W : ℝ) := Nat.le_ceil r
  have hWr : (W : ℝ) ≤ 2 * r := by
    have h := Nat.ceil_lt_add_one hr0
    dsimp only [W]
    linarith
  have hr8 : r ^ (8 : ℕ) = (n : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hr5 : r ^ (5 : ℕ) = (n : ℝ) ^ (5 / 8 : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  refine ⟨W, ?_, ?_⟩
  · have hp := pow_le_pow_left₀ hr0 hrW 8
    rw [hr8] at hp
    exact_mod_cast hp
  · calc
      (W : ℝ) ^ 5 ≤ (2 * r) ^ 5 := pow_le_pow_left₀ (by positivity) hWr 5
      _ = 32 * (n : ℝ) ^ (5 / 8 : ℝ) := by rw [mul_pow, hr5]; norm_num

/-- The three-dimensional construction at every positive cardinality. -/
theorem exists_three_dimensional_construction {n : ℕ} (hn : 0 < n) :
    ∃ F : Finset (Fin 3 → ℤ), F.card = n ∧
      ((integerPositiveDifferences F).card : ℝ) ≤ 480 * (n : ℝ) ^ (5 / 8 : ℝ) := by
  obtain ⟨W, hW, hpower⟩ := exists_eighth_power_size hn
  obtain ⟨F, hF, hD, _hΔ⟩ := exists_three_dimensional_power_construction W
  obtain ⟨A, hAF, hA⟩ := Finset.exists_subset_card_eq (hW.trans hF.symm.le)
  refine ⟨A, hA, ?_⟩
  have hmono := Finset.card_le_card (integerPositiveDifferences_mono hAF)
  have hbound : ((integerPositiveDifferences A).card : ℝ) ≤ 15 * (W : ℝ) ^ 5 := by
    exact_mod_cast hmono.trans hD
  nlinarith

end
end Erdos539Geometry
