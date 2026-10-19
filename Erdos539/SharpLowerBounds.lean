/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpLower
import Erdos539.SharpUpper

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- Power form of the sharp lower bound, retaining both explicit loss factors. -/
theorem power_bound_of_sharp_log_bound {n q d N : ℕ} (hn : 0 < n) (hq : 0 < q) (e : ℝ)
    (h : e * Real.log n - 8 * (d : ℝ) * Real.log 2 -
      sharpLogLoss d * Real.log (dyadicLevels N) ≤ Real.log q) :
    (n : ℝ) ^ e / ((256 : ℝ) ^ d * (dyadicLevels N : ℝ) ^ sharpLogLoss d) ≤ q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hL : (0 : ℝ) < dyadicLevels N := by
    exact_mod_cast (show 0 < dyadicLevels N by unfold dyadicLevels; omega)
  have hpow : 0 < (n : ℝ) ^ e := Real.rpow_pos_of_pos hn' e
  have hLpow : 0 < (dyadicLevels N : ℝ) ^ sharpLogLoss d := Real.rpow_pos_of_pos hL _
  have hden : (0 : ℝ) < (256 : ℝ) ^ d := by positivity
  apply (Real.log_le_log_iff (div_pos hpow (mul_pos hden hLpow)) hq').mp
  rw [Real.log_div hpow.ne' (mul_pos hden hLpow).ne', Real.log_mul hden.ne' hLpow.ne',
    Real.log_rpow hn', Real.log_rpow hL, Real.log_pow]
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 8
    norm_num at hh
    exact hh
  rw [h256]
  nlinarith

theorem sharp_fan_lower_bound {ι : Type*} [Fintype ι] (hd : 0 < Fintype.card ι)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      ((256 : ℝ) ^ Fintype.card ι * (dyadicLevels F.card : ℝ) ^ sharpLogLoss (Fintype.card ι)) ≤ maxFan F := by
  exact power_bound_of_sharp_log_bound hF.card_pos
    (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF)) _
    (sharp_log_fan_lower_bound (Fintype.card ι) ι rfl hd F.card F hF le_rfl)

theorem integer_sharp_log_lower_bound {d : ℕ} (hd : 0 < d)
    {F : Finset (Fin d → ℤ)} (hF : F.Nonempty) :
    (sharpExponent d : ℝ) * Real.log F.card - 8 * (d : ℝ) * Real.log 2 -
      sharpLogLoss d * Real.log (dyadicLevels F.card) ≤ Real.log (integerPositiveDifferences F).card := by
  letI : DecidableEq (Fin d → ℝ) := Classical.decEq _
  have hf := hF.image integerToReal
  have h := sharp_log_fan_lower_bound d (Fin d) (by simp only [Fintype.card_fin]) hd
    (F.image integerToReal).card (F.image integerToReal) hf le_rfl
  have hM : (0 : ℝ) < maxFan (F.image integerToReal) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hf))
  have hmono := Real.log_le_log hM (show (maxFan (F.image integerToReal) : ℝ) ≤
      (posDiff (F.image integerToReal)).card by exact_mod_cast maxFan_le_card_posDiff _)
  rw [posDiff_integerToReal_card] at hmono
  rw [integerToReal_image_card] at h
  exact h.trans hmono

theorem fixedDimensionalMinimum_sharp_log_lower {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (sharpExponent d : ℝ) * Real.log n - 8 * (d : ℝ) * Real.log 2 -
      sharpLogLoss d * Real.log (dyadicLevels n) ≤ Real.log (fixedDimensionalMinimum d n) := by
  obtain ⟨_C, _hC, hfamily⟩ := exists_sharp_upper_construction hd
  obtain ⟨A, hA, _hD⟩ := hfamily n hn
  obtain ⟨F, hF, hq⟩ := fixedDimensionalMinimum_attained ⟨A, hA⟩
  have hFn : F.Nonempty := Finset.card_pos.mp (by omega)
  have h := integer_sharp_log_lower_bound hd hFn
  rwa [hF, hq] at h

theorem fixedDimensionalMinimum_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < fixedDimensionalMinimum d n := by
  obtain ⟨_C, _hC, hfamily⟩ := exists_sharp_upper_construction hd
  obtain ⟨A, hA, _hD⟩ := hfamily n hn
  obtain ⟨F, hF, hq⟩ := fixedDimensionalMinimum_attained ⟨A, hA⟩
  have hFn : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hFn
  rw [← hq]
  apply Finset.card_pos.mpr
  exact ⟨intPdiff x x, mem_integerPositiveDifferences.mpr ⟨x, hx, x, hx, rfl⟩⟩

/-- Matching exponents in every dimension, with the explicit lower logarithmic loss. -/
theorem fixedDimensionalMinimum_sharp_bounds {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (sharpExponent d : ℝ) /
        ((256 : ℝ) ^ d * (dyadicLevels n : ℝ) ^ sharpLogLoss d) ≤ fixedDimensionalMinimum d n ∧
      (fixedDimensionalMinimum d n : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := fixedDimensionalMinimum_sharp_upper hd
  refine ⟨C, hC, ?_⟩
  intro n hn
  exact ⟨power_bound_of_sharp_log_bound hn (fixedDimensionalMinimum_pos hd hn) _
    (fixedDimensionalMinimum_sharp_log_lower hd hn), hupper n hn⟩

theorem primeSupportedMinimum_sharp_bounds {d : ℕ} (hd : 0 < d)
    (p : Fin d ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (sharpExponent d : ℝ) /
        ((256 : ℝ) ^ d * (dyadicLevels n : ℝ) ^ sharpLogLoss d) ≤ primeSupportedMinimum p n ∧
      (primeSupportedMinimum p n : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  simpa only [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp] using
    fixedDimensionalMinimum_sharp_bounds hd

end
end Erdos539Geometry
