/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GrowthBasics
import Erdos539.ElementaryDimension
import Erdos539.UniformRegularity
import Erdos539.PFRLogEstimate

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- Quantitative growth inequality from elementary original-coordinate extraction.
The asymptotic inversion and the zero-inclusive threshold transfer are separate. -/
theorem elementary_integer_log_growth [Fintype ι] {F : Finset (ι → ℤ)} (hF : F.Nonempty) :
    Real.log F.card ≤
      2000000 * (growthParameter F.card (integerPositiveDifferences F).card) ^ 2 *
        (1 + Real.log (growthParameter F.card (integerPositiveDifferences F).card + 1)) := by
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
    exists_elementary_integer_dimension_subset F hF hKone hDiff
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hBlog : Real.log F.card - 17 * T ≤ Real.log B.card := by
    have hden : (0 : ℝ) < 1024 * K ^ 10 := by positivity
    have hl := Real.log_le_log (div_pos hn hden) hBsize
    rw [Real.log_div hn.ne' hden.ne', Real.log_mul (by norm_num) (pow_ne_zero _ hK.ne'),
      Real.log_pow] at hl
    have h1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
      have hh := Real.log_pow (2 : ℝ) 10
      norm_num at hh
      exact hh
    rw [h1024] at hl
    norm_num only [Nat.cast_ofNat] at hl
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
    change Real.log F.card ≤ 2000000 * T ^ 2 * (1 + Real.log (T + 1))
    exact pfr_log_estimate_singleton hT (by linarith)
  have hdpos : 0 < d := by
    by_contra hh
    have hd0 : d = 0 := by omega
    subst d
    have hc : B.card ≤ 1 := Finset.card_le_one.mpr (fun _ _ _ _ ↦ Subsingleton.elim _ _)
    exact hsmall hc
  have hdT : (d : ℝ) ≤ 100 * T := by
    have hlog2K2 : Real.log (2 * K ^ 2) = Real.log 2 + 2 * Real.log K := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hK.ne'), Real.log_pow]
      norm_num
    have hratio : 0 ≤ Real.log (2 * K ^ 2) / Real.log 2 := by
      rw [hlog2K2]
      positivity
    have hratioBound : Real.log (2 * K ^ 2) / Real.log 2 ≤ 4 * T := by
      apply (div_le_iff₀ log_two_pos).mpr
      rw [hlog2K2]
      nlinarith
    have hceil := (Nat.ceil_lt_add_one hratio).le
    have hd' : (d : ℝ) ≤ (extractionSupport (K ^ 2) : ℝ) := by exact_mod_cast hd
    change (extractionSupport (K ^ 2) : ℝ) ≤ Real.log (2 * K ^ 2) / Real.log 2 + 1 at hceil
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
  have hregular := uniform_log_bound hB (by simpa only [Fintype.card_fin] using hdpos)
    (integerDifferences F).card (fun J ↦ (projection_mul_maxFiber_le_differences B J).trans hBdiff)
  simp only [Fintype.card_fin] at hregular
  exact pfr_log_estimate hdpos (Real.log_natCast_nonneg _) hT hdT hBlog hHlog hQlog
    (hregular.trans hMlog)

end
end Erdos539Geometry
