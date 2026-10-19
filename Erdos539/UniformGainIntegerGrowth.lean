/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerGrowth
import Erdos539.UniformGainEstimates

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

theorem real_card_le_differences {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    F.card ≤ (differences F).card := by
  obtain ⟨a, ha⟩ := hF
  apply Finset.card_le_card_of_injOn (fun x ↦ x - a)
  · intro x hx
    exact mem_differences.mpr ⟨x, hx, a, ha, rfl⟩
  · intro x _hx y _hy hxy
    exact sub_left_injective hxy

/-- A hypothetical uniform 1/d gain, combined with the actual checked PFR
 theorem, implies a quadratic logarithmic growth estimate. -/
theorem UniformLogGainHypothesis.integer_log_growth [Fintype ι] {U V c : ℝ}
    (hgain : UniformLogGainHypothesis U V c) (hU : 1 ≤ U) (hV : 0 ≤ V)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) {F : Finset (ι → ℤ)} (hF : F.Nonempty) :
    Real.log F.card ≤ uniformGainGrowthConstant U V c *
      (growthParameter F.card (integerPositiveDifferences F).card) ^ 2 := by
  classical
  let q := (integerPositiveDifferences F).card
  let K : ℝ := (q : ℝ) ^ 2 / F.card
  let T := Real.log (2 * K)
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hnsq : F.card ≤ q ^ 2 := card_le_integerPositiveDifferences_sq hF
  have hqNat : 0 < q := by have := hF.card_pos; nlinarith
  have hq : (0 : ℝ) < q := by exact_mod_cast hqNat
  have hKone : 1 ≤ K := by
    apply (le_div_iff₀ hn).mpr
    simpa only [one_mul, Nat.cast_pow] using (show (F.card : ℝ) ≤ (q ^ 2 : ℕ) by exact_mod_cast hnsq)
  have hK : 0 < K := by linarith
  have hKn : K * F.card = (q : ℝ) ^ 2 := div_mul_cancel₀ _ hn.ne'
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKone
  have hTdef : T = Real.log 2 + Real.log K := Real.log_mul (by norm_num) hK.ne'
  have hlog2low : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hT : 1 / 2 ≤ T := by linarith
  have hKT : Real.log K ≤ T := by linarith [log_two_pos]
  have hDiff : ((integerDifferences F).card : ℝ) ≤ K * F.card := by
    rw [hKn]
    exact_mod_cast integerDifferences_card_le F
  obtain ⟨d, hd, B, hB, hBsize, hBposDiff, hBdiff⟩ :=
    Erdos539Dimension.exists_small_dimension_subset F hF K hDiff
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hBlog : Real.log F.card - 17 * T ≤ Real.log B.card := by
    have hl := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hK (-17 : ℝ)) hn) hBsize
    rw [Real.log_mul (Real.rpow_pos_of_pos hK (-17 : ℝ)).ne' hn.ne', Real.log_rpow hK] at hl
    linarith
  have hQlog : Real.log q ≤ (Real.log F.card + T) / 2 := by
    have he := congrArg Real.log hKn
    rw [Real.log_mul hK.ne' hn.ne', Real.log_pow] at he
    norm_num at he
    linarith
  by_cases hsmall : B.card ≤ 1
  · have hb0 : Real.log B.card ≤ 0 := by
      have hl := Real.log_le_log hb (show (B.card : ℝ) ≤ 1 by exact_mod_cast hsmall)
      simpa only [Real.log_one] using hl
    change Real.log F.card ≤ uniformGainGrowthConstant U V c * T ^ 2
    exact uniform_gain_pfr_singleton hU hV hc hc1 hT (by linarith)
  have hdpos : 0 < d := by
    by_contra hh
    have hd0 : d = 0 := by omega
    subst d
    have hc : B.card ≤ 1 := Finset.card_le_one.mpr (fun _ _ _ _ ↦ Subsingleton.elim _ _)
    exact hsmall hc
  have hdT : (d : ℝ) ≤ 100 * T := by
    have hC : (0 : ℝ) ≤ 40 / Real.log 2 := by positivity
    have hCbound : (40 : ℝ) / Real.log 2 ≤ 80 := by
      apply (div_le_iff₀ log_two_pos).mpr
      linarith
    have hceil := Nat.ceil_lt_add_one (mul_nonneg hC hlogK)
    have hd' : (d : ℝ) ≤ (⌈(40 / Real.log 2) * Real.log K⌉₊ : ℕ) := by exact_mod_cast hd
    have hmul := mul_le_mul_of_nonneg_right hCbound hlogK
    linarith
  have hHpos : (0 : ℝ) < (integerDifferences F).card := by
    exact_mod_cast hF.card_pos.trans_le (card_le_integerDifferences hF)
  have hHlog : Real.log (integerDifferences F).card ≤ Real.log F.card + T := by
    have hl := Real.log_le_log hHpos hDiff
    rw [Real.log_mul hK.ne' hn.ne'] at hl
    linarith
  have hMpos : (0 : ℝ) < maxFan B := by
    exact_mod_cast (show 0 < maxFan B from lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hB))
  have hMlog : Real.log (maxFan B) ≤ Real.log q :=
    Real.log_le_log hMpos (by exact_mod_cast (maxFan_le_card_posDiff B).trans hBposDiff)
  let Kchild : ℝ := (integerDifferences F).card / B.card
  have hcardH : B.card ≤ (integerDifferences F).card := (real_card_le_differences hB).trans hBdiff
  have hKchild : 1 ≤ Kchild := by
    apply (le_div_iff₀ hb).mpr
    simpa only [one_mul] using (show (B.card : ℝ) ≤ (integerDifferences F).card by exact_mod_cast hcardH)
  have hchildD : ((differences B).card : ℝ) ≤ Kchild * B.card := by
    rw [div_mul_cancel₀ _ hb.ne']
    exact_mod_cast hBdiff
  have hchildLog : Real.log Kchild ≤ 18 * T := by
    rw [Real.log_div hHpos.ne' hb.ne']
    linarith
  have hregular := hgain d hdpos B hB Kchild hKchild hchildD
  exact uniform_gain_pfr_scalar hdpos hU hV hc hc1 (Real.log_natCast_nonneg _) hT hdT
    hBlog hQlog hchildLog (hregular.trans hMlog)

end
end Erdos539Geometry
