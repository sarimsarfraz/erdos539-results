/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpRegularityBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- Explicit gain over 1/2 supplied by the exact split recursion. -/
theorem sharpExponent_ge_half_add_exact {d : ℕ} (hd : 0 < d) :
    (1 : ℝ) / 2 + 1 / (4 * (d : ℝ) - 2) ≤ (sharpExponent d : ℝ) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 1 := by linarith
  have he : uniformExponent d = (1 : ℝ) / 2 + 1 / (4 * (d : ℝ) - 2) := by
    unfold uniformExponent
    rw [show 4 * (d : ℝ) - 2 = 2 * (2 * d - 1) by ring]
    field_simp (disch := linarith)
    ring
  exact he ▸ sharpExponent_ge_uniform hd

theorem regularityGainDenominator_eq {d : ℕ} (hd : 2 ≤ d) :
    regularityGainDenominator d = 2 + Real.log d / Real.log 2 := by
  rw [regularityGainDenominator, sharpRegularityCost, if_neg (by omega), regularityCost]
  ring

theorem fiberIrregularity_le_differences {ι : Type*} [Fintype ι] (S : Finset (ι → ℝ)) :
    fiberIrregularity S ≤ (differences S).card / (S.card : ℝ) := by
  have h : maxProjectionFiberProduct S ≤ (differences S).card :=
    Finset.sup_le (fun I _ ↦ projection_mul_maxFiber_le_differences S I)
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg _)

theorem fiberIrregularity_le_posDiff_sq {ι : Type*} [Fintype ι] (S : Finset (ι → ℝ)) :
    fiberIrregularity S ≤ ((posDiff S).card : ℝ) ^ 2 / (S.card : ℝ) := by
  apply (fiberIrregularity_le_differences S).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast differences_card_le_posDiff_sq S) (Nat.cast_nonneg _)

/-- The fully explicit dimension-uniform corollary, with gain of order
1/(d log d) and the manuscript's exact constant. -/
theorem explicit_uniform_difference_bound {ι : Type*} [Fintype ι]
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) (hd : 0 < Fintype.card ι) :
    (F.card : ℝ) ^ (1 / 2 + 1 /
      ((4 * (Fintype.card ι : ℝ) - 2) * regularityGainDenominator (Fintype.card ι))) /
      (256 : ℝ) ^ ((Fintype.card ι : ℝ) / regularityGainDenominator (Fintype.card ι)) ≤ (posDiff F).card := by
  have hB : 0 < regularityGainDenominator (Fintype.card ι) := by
    unfold regularityGainDenominator
    linarith [sharpRegularityCost_nonneg hd]
  have he : 1 / ((4 * (Fintype.card ι : ℝ) - 2) * regularityGainDenominator (Fintype.card ι)) ≤
      ((sharpExponent (Fintype.card ι) : ℝ) - 1 / 2) / regularityGainDenominator (Fintype.card ι) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right (by linarith [sharpExponent_ge_half_add_exact hd]) hB.le
  have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ F.card by exact_mod_cast hF.card_pos)
    (show 1 / 2 + 1 / ((4 * (Fintype.card ι : ℝ) - 2) * regularityGainDenominator (Fintype.card ι)) ≤
      1 / 2 + ((sharpExponent (Fintype.card ι) : ℝ) - 1 / 2) / regularityGainDenominator (Fintype.card ι) by linarith)
  have hc : (0 : ℝ) ≤ (256 : ℝ) ^ ((Fintype.card ι : ℝ) / regularityGainDenominator (Fintype.card ι)) :=
    Real.rpow_nonneg (by norm_num) _
  exact (div_le_div_of_nonneg_right hp hc).trans (sharp_uniform_difference_bound hF hd)

end
end Erdos539Geometry
