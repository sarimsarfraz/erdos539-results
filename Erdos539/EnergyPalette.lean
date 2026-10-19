/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyNormLower
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance energyPaletteDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem posDiff_card_pos {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    0 < (posDiff S).card :=
  lt_of_lt_of_le Nat.zero_lt_one ((one_le_maxFan hS).trans (maxFan_le_card_posDiff S))

theorem card_le_real_differences {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    S.card ≤ (differences S).card := by
  obtain ⟨a, ha⟩ := hS
  apply Finset.card_le_card_of_injOn (fun x ↦ x - a)
  · intro x hx
    exact mem_differences.mpr ⟨x, hx, a, ha, rfl⟩
  · intro x _ y _ hxy
    exact sub_left_inj.mp hxy

theorem card_le_real_posDiff_sq {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    S.card ≤ (posDiff S).card ^ 2 :=
  (card_le_real_differences hS).trans (differences_card_le_posDiff_sq S)

theorem energyNorm_le_palette_sq {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    energyNorm S ≤ ((posDiff S).card : ℝ) ^ 2 := by
  exact (energyNorm_le_card S).trans (by exact_mod_cast card_le_real_posDiff_sq hS)

theorem card_sq_le_palette_sq_mul_energyNorm {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    (S.card : ℝ) ^ 2 ≤ ((posDiff S).card : ℝ) ^ 2 * energyNorm S := by
  have heq : S - S = differences S := by
    ext z
    simp only [Finset.mem_sub, mem_differences]
  have hn := card_sq_le_difference_mul_energyNorm hS
  rw [heq] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast differences_card_le_posDiff_sq S) (energyNorm_nonneg S))

theorem energyNorm_log_lower_palette {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    2 * Real.log S.card - 2 * Real.log (posDiff S).card ≤ Real.log (energyNorm S) := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hq : (0 : ℝ) < (posDiff S).card := by exact_mod_cast posDiff_card_pos hS
  have h := Real.log_le_log (pow_pos hN 2) (card_sq_le_palette_sq_mul_energyNorm hS)
  rw [Real.log_mul (pow_pos hq 2).ne' (energyNorm_pos hS).ne', Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

@[simp] theorem posDiff_singleton (x : ι → ℝ) : posDiff {x} = {0} := by
  simp [posDiff]

end
end Erdos539Geometry
