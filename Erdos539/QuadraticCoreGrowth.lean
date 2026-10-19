/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreBounds
import Erdos539.ElementaryDimension
import Erdos539.GrowthBasics

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
local instance quadraticCoreGrowthDecidableEq (D : ℕ) : DecidableEq (Fin D → ℝ) := Classical.decEq _

/-- The unresolved quadratic core hypothesis, stated for actual cores
selected from every finite positive-dimensional parent. It is an explicit
argument of the sufficient implication, not an axiom of this development. -/
def QuadraticCoreHypothesis (C : ℝ) : Prop :=
  ∀ (D : ℕ), 0 < D → ∀ (S : Finset (Fin D → ℝ)), S.Nonempty →
    ∀ (I : Finset (Fin D)) (T : Finset (Fin D → ℝ)),
      IsProjectionCriticalCore S (4 * (D : ℝ)) I T → Real.log (energyNorm T) ≤ C * (D : ℝ) ^ 2

/-- Elementary extraction and the actual critical-core retention theorem
turn the explicit quadratic hypothesis into the required global log bound. -/
theorem QuadraticCoreHypothesis.integer_log_growth {C : ℝ} (hcore : QuadraticCoreHypothesis C)
    (hC : 0 ≤ C) {ι : Type*} [Fintype ι] {F : Finset (ι → ℤ)} (hF : F.Nonempty) :
    Real.log F.card ≤ (10000 * C + 14470) *
      (growthParameter F.card (integerPositiveDifferences F).card) ^ 2 := by
  classical
  letI : DecidableEq (ι → ℝ) := Classical.decEq _
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
    change Real.log F.card ≤ (10000 * C + 14470) * T ^ 2
    have hlinear : 17 * T ≤ 34 * T ^ 2 := by nlinarith
    have hconst : 34 ≤ 10000 * C + 14470 := by linarith
    have hm := mul_le_mul_of_nonneg_right hconst (sq_nonneg T)
    linarith
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
  letI : DecidableEq (Fin d → ℝ) := Classical.decEq _
  have hqB : (0 : ℝ) < (posDiff B).card := by exact_mod_cast posDiff_card_pos hB
  have hqBlog : Real.log (posDiff B).card ≤ Real.log q :=
    Real.log_le_log hqB (by exact_mod_cast hBposDiff)
  have hchild : Real.log (paletteSurplus B) ≤ 18 * T := by
    rw [log_paletteSurplus hB]
    linarith
  obtain ⟨I, A, hA⟩ := exists_projectionCriticalCore hB (4 * (d : ℝ))
  have hbcore : 0 < 4 * (d : ℝ) := by positivity
  have hretain := hA.log_retention hB hbcore
  have hmul := mul_le_mul_of_nonneg_left hchild (by positivity : 0 ≤ 8 * (d : ℝ) + 1)
  have hret : Real.log B.card - (8 * (d : ℝ) + 1) * (18 * T) ≤ Real.log (energyNorm A) := by
    nlinarith
  have hbound := hcore d hdpos B hB I A hA
  exact quadratic_core_scalar_growth hT hC hdT hBlog hret hbound

end
end Erdos539Geometry
