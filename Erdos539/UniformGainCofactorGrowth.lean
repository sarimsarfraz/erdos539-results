/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.UniformGainIntegerGrowth
import Erdos539.CofactorGrowth

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

theorem UniformLogGainHypothesis.positive_log_growth {U V c : ℝ}
    (hgain : UniformLogGainHypothesis U V c) (hU : 1 ≤ U) (hV : 0 ≤ V)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) {A : Finset ℕ}
    (hA : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a) :
    Real.log A.card ≤ uniformGainGrowthConstant U V c * (growthParameter A.card (cofactors A).card) ^ 2 := by
  have hF : (integerExponentSet A).Nonempty := Finset.card_pos.mp (by
    rw [integerExponentSet_card hpos]
    exact hA.card_pos)
  simpa only [integerExponentSet_card hpos, integerPositiveDifferences_integerExponentSet_card hpos]
    using hgain.integer_log_growth hU hV hc hc1 hF

/-- The conditional quadratic estimate transfers to sets containing zero,
using the same exact threshold convention as the unconditional result. -/
theorem UniformLogGainHypothesis.cofactor_log_growth {U V c : ℝ}
    (hgain : UniformLogGainHypothesis U V c) (hU : 1 ≤ U) (hV : 0 ≤ V)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) {A : Finset ℕ} (hn : 2 ≤ A.card) :
    Real.log 2 ≤ thresholdGrowthParameter A.card (cofactors A).card ∧
      Real.log A.card ≤ (uniformGainGrowthConstant U V c + 4) *
        (thresholdGrowthParameter A.card (cofactors A).card) ^ 2 := by
  classical
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B, hBA, hBcard, hBpos⟩ := Erdos539.positive_subset_pred hA
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  have hn' : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb' : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hn2b : (A.card : ℝ) ≤ 2 * B.card := by exact_mod_cast (show A.card ≤ 2 * B.card by omega)
  have hQB : B.card ≤ (cofactors B).card ^ 2 := positive_card_le_cofactors_sq hB hBpos
  have hqbNat : 0 < (cofactors B).card := by have := hB.card_pos; nlinarith
  have hqb : (0 : ℝ) < (cofactors B).card := by exact_mod_cast hqbNat
  have hqmono : ((cofactors B).card : ℝ) ≤ (cofactors A).card := by
    exact_mod_cast Finset.card_le_card (Erdos539.cofactors_mono hBA)
  let x := growthParameter B.card (cofactors B).card
  let y := thresholdGrowthParameter A.card (cofactors A).card
  have hx : Real.log 2 ≤ x := growthParameter_lower hB.card_pos hQB
  have hxy : x ≤ y := by
    apply Real.log_le_log (show 0 < 2 * (((cofactors B).card : ℝ) ^ 2 / B.card) by positivity)
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ hb' hn').mpr
    have hqSq : ((cofactors B).card : ℝ) ^ 2 ≤ ((cofactors A).card : ℝ) ^ 2 := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_right hqSq hn'.le
    have h₂ := mul_le_mul_of_nonneg_left hn2b (sq_nonneg ((cofactors A).card : ℝ))
    nlinarith
  refine ⟨hx.trans hxy, ?_⟩
  have hx0 : 0 ≤ x := log_two_pos.le.trans hx
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hC : 0 ≤ uniformGainGrowthConstant U V c :=
    le_trans (by norm_num) (uniformGainGrowthConstant_ge hU hV hc hc1)
  have hBbound : Real.log B.card ≤ uniformGainGrowthConstant U V c * y ^ 2 := by
    have h := hgain.positive_log_growth hU hV hc hc1 hB hBpos
    change Real.log B.card ≤ uniformGainGrowthConstant U V c * x ^ 2 at h
    have hs : x ^ 2 ≤ y ^ 2 := by nlinarith
    exact h.trans (mul_le_mul_of_nonneg_left hs hC)
  have hlogn := Real.log_le_log hn' hn2b
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hb'.ne'] at hlogn
  have hl2low : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hl2high : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hyhalf : 1 / 2 ≤ y := hl2low.trans (hx.trans hxy)
  change Real.log A.card ≤ (uniformGainGrowthConstant U V c + 4) * y ^ 2
  nlinarith

end
end Erdos539Geometry
