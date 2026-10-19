/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PowerInterpolation

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- Rounding up a positive a-th root controls every integral b-th power. -/
theorem exists_power_size {a n : ℕ} (ha : 0 < a) (hn : 0 < n) (b : ℕ) :
    ∃ W : ℕ, n ≤ W ^ a ∧
      (W : ℝ) ^ b ≤ (2 : ℝ) ^ b * (n : ℝ) ^ ((b : ℝ) / a) := by
  let r : ℝ := (n : ℝ) ^ (1 / (a : ℝ))
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hr1 : 1 ≤ r := Real.one_le_rpow hn1 (by positivity)
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr1
  let W := Nat.ceil r
  have hrW : r ≤ (W : ℝ) := Nat.le_ceil r
  have hWr : (W : ℝ) ≤ 2 * r := by
    have h := Nat.ceil_lt_add_one hr0
    dsimp only [W]
    linarith
  have hra : r ^ a = (n : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0, one_div_mul_cancel ha0.ne', Real.rpow_one]
  have hrb : r ^ b = (n : ℝ) ^ ((b : ℝ) / a) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    congr 1
    ring
  refine ⟨W, ?_, ?_⟩
  · have hp := pow_le_pow_left₀ hr0 hrW a
    rw [hra] at hp
    exact_mod_cast hp
  · calc
      (W : ℝ) ^ b ≤ (2 * r) ^ b := pow_le_pow_left₀ (by positivity) hWr b
      _ = _ := by rw [mul_pow, hrb]

/-- The passage from power-sized families to arbitrary cardinalities works
in every positive integral size exponent. -/
theorem interpolate_integer_construction {d a b C : ℕ} (ha : 0 < a)
    (hfamily : ∀ W : ℕ, ∃ F : Finset (Fin d → ℤ), F.card = W ^ a ∧
      (integerPositiveDifferences F).card ≤ C * W ^ b) {n : ℕ} (hn : 0 < n) :
    ∃ F : Finset (Fin d → ℤ), F.card = n ∧
      ((integerPositiveDifferences F).card : ℝ) ≤
        ((C : ℝ) * 2 ^ b) * (n : ℝ) ^ ((b : ℝ) / a) := by
  obtain ⟨W, hW, hpower⟩ := exists_power_size ha hn b
  obtain ⟨F, hF, hD⟩ := hfamily W
  obtain ⟨A, hAF, hA⟩ := Finset.exists_subset_card_eq (hW.trans hF.symm.le)
  refine ⟨A, hA, ?_⟩
  have hbound : ((integerPositiveDifferences A).card : ℝ) ≤ C * (W : ℝ) ^ b := by
    exact_mod_cast (Finset.card_le_card (integerPositiveDifferences_mono hAF)).trans hD
  calc
    _ ≤ (C : ℝ) * (W : ℝ) ^ b := hbound
    _ ≤ (C : ℝ) * (2 ^ b * (n : ℝ) ^ ((b : ℝ) / a)) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by ring

end
end Erdos539Geometry
