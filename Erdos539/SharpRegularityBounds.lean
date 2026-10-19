/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpRegularity
import Erdos539.SharpExponentBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

/-- The unnormalized maximum projection-size times largest-fiber-size. -/
def maxProjectionFiberProduct (S : Finset (ι → ℝ)) : ℕ :=
  (Finset.univ : Finset (Finset ι)).sup (fun I ↦ (projection S I).card * maxFiber S (project I))

/-- The manuscript's fiber irregularity R(S). -/
def fiberIrregularity (S : Finset (ι → ℝ)) : ℝ :=
  (maxProjectionFiberProduct S : ℝ) / S.card

theorem projection_product_le_max (S : Finset (ι → ℝ)) (I : Finset ι) :
    (projection S I).card * maxFiber S (project I) ≤ maxProjectionFiberProduct S :=
  Finset.le_sup (f := fun I ↦ (projection S I).card * maxFiber S (project I)) (Finset.mem_univ I)

theorem card_le_maxProjectionFiberProduct {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    S.card ≤ maxProjectionFiberProduct S :=
  parent_card_le_of_fiber_bound hS (projection_product_le_max S)

theorem one_le_fiberIrregularity {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    1 ≤ fiberIrregularity S := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  apply (le_div_iff₀ hn).mpr
  simpa only [one_mul] using (show (S.card : ℝ) ≤ maxProjectionFiberProduct S by
    exact_mod_cast card_le_maxProjectionFiberProduct hS)

/-- The sharp regularity theorem, with the exact manuscript irregularity and alpha_d. -/
theorem sharp_regularity_fan_lower_bound {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (hd : 0 < Fintype.card ι) :
    (S.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      ((256 : ℝ) ^ Fintype.card ι * fiberIrregularity S ^ sharpRegularityCost (Fintype.card ι)) ≤ maxFan S := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hH : (0 : ℝ) < maxProjectionFiberProduct S := by
    exact_mod_cast hS.card_pos.trans_le (card_le_maxProjectionFiberProduct hS)
  have hR : 0 < fiberIrregularity S := lt_of_lt_of_le (by norm_num) (one_le_fiberIrregularity hS)
  have hRpow := Real.rpow_pos_of_pos hR (sharpRegularityCost (Fintype.card ι))
  have hnPow := Real.rpow_pos_of_pos hn (sharpExponent (Fintype.card ι) : ℝ)
  have hc : (0 : ℝ) < (256 : ℝ) ^ Fintype.card ι := by positivity
  have hM : (0 : ℝ) < maxFan S := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hS))
  have h := sharp_regularity_log_bound hS hd (maxProjectionFiberProduct S) (projection_product_le_max S)
  have hlogR : Real.log (fiberIrregularity S) = Real.log (maxProjectionFiberProduct S) - Real.log S.card :=
    Real.log_div hH.ne' hn.ne'
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 8
    norm_num at hh
    exact hh
  apply (Real.log_le_log_iff (div_pos hnPow (mul_pos hc hRpow)) hM).mp
  rw [Real.log_div hnPow.ne' (mul_pos hc hRpow).ne', Real.log_mul hc.ne' hRpow.ne',
    Real.log_rpow hn, Real.log_rpow hR, Real.log_pow, h256, hlogR]
  dsimp only [sharpExponentReal] at h
  nlinarith

/-- The denominator controlling the gain over the square-root exponent. -/
def regularityGainDenominator (d : ℕ) : ℝ := 1 + 2 * sharpRegularityCost d

/-- The manuscript's sharp uniform corollary for arbitrary finite sets. -/
theorem sharp_uniform_difference_bound {F : Finset (ι → ℝ)} (hF : F.Nonempty)
    (hd : 0 < Fintype.card ι) :
    (F.card : ℝ) ^ (1 / 2 + ((sharpExponent (Fintype.card ι) : ℝ) - 1 / 2) /
      regularityGainDenominator (Fintype.card ι)) /
      (256 : ℝ) ^ ((Fintype.card ι : ℝ) / regularityGainDenominator (Fintype.card ι)) ≤ (posDiff F).card := by
  let d := Fintype.card ι
  let B := regularityGainDenominator d
  have hB : 0 < B := by
    dsimp only [B, regularityGainDenominator]
    linarith [sharpRegularityCost_nonneg hd]
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hM : (0 : ℝ) < maxFan F := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
  have hq : (0 : ℝ) < (posDiff F).card :=
    hM.trans_le (by exact_mod_cast maxFan_le_card_posDiff F)
  have h := sharp_regularity_log_bound hF hd ((posDiff F).card ^ 2) (projection_mul_maxFiber_le_posDiff_sq F)
  rw [Nat.cast_pow, Real.log_pow] at h
  have hmono := Real.log_le_log hM (show (maxFan F : ℝ) ≤ (posDiff F).card by exact_mod_cast maxFan_le_card_posDiff F)
  have hclosed : (((sharpExponent d : ℝ) + sharpRegularityCost d) * Real.log F.card -
      8 * (d : ℝ) * Real.log 2) / B ≤ Real.log (posDiff F).card := by
    apply (div_le_iff₀ hB).mpr
    dsimp only [B, regularityGainDenominator, d, sharpExponentReal] at *
    norm_num only [Nat.cast_ofNat] at h
    nlinarith
  have he : 1 / 2 + ((sharpExponent d : ℝ) - 1 / 2) / B =
      ((sharpExponent d : ℝ) + sharpRegularityCost d) / B := by
    have hne : 1 + 2 * sharpRegularityCost d ≠ 0 := hB.ne'
    dsimp only [B, regularityGainDenominator]
    field_simp [hne]
    ring
  change (F.card : ℝ) ^ (1 / 2 + ((sharpExponent d : ℝ) - 1 / 2) / B) /
    (256 : ℝ) ^ ((d : ℝ) / B) ≤ _
  rw [he]
  have hp := Real.rpow_pos_of_pos hn (((sharpExponent d : ℝ) + sharpRegularityCost d) / B)
  have hc := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 256) ((d : ℝ) / B)
  apply (Real.log_le_log_iff (div_pos hp hc) hq).mp
  rw [Real.log_div hp.ne' hc.ne', Real.log_rpow hn, Real.log_rpow (by norm_num : (0 : ℝ) < 256)]
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 8
    norm_num at hh
    exact hh
  rw [h256]
  calc
    _ = (((sharpExponent d : ℝ) + sharpRegularityCost d) * Real.log F.card -
        8 * (d : ℝ) * Real.log 2) / B := by ring
    _ ≤ _ := hclosed

end
end Erdos539Geometry
