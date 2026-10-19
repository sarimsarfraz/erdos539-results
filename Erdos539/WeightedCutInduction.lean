/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedCutHypothesis
import Erdos539.WeightedCutEstimates
import Erdos539.WeightedPruningLog
import Erdos539.EnergyDecidableInvariance

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
local instance weightedCutInductionDecidableEq (ι : Type) : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The weighted-cut hypothesis gives the exact sharp exponent with a loss
exponential in dimension. The proof uses the actual weighted-pruning theorem
and one exact optimizer per parent. -/
theorem WeightedProjectionBalanceHypothesis.log_fan_bound {B : ℝ}
    (hcut : WeightedProjectionBalanceHypothesis B) (hB : 0 ≤ B) :
    ∀ d : ℕ, 0 < d → ∀ (ι : Type) [Fintype ι], Fintype.card ι = d →
      ∀ S : Finset (ι → ℝ), S.Nonempty →
        (sharpExponent d : ℝ) * Real.log (energyNorm S) - (B + Real.log 16) * d ≤
          Real.log (maxFan S) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd ι _ hdim S hS
    let A := B + Real.log 16
    have hA : 0 ≤ A := add_nonneg hB (Real.log_nonneg (by norm_num))
    have hlam := energyNorm_pos hS
    have hL : 0 ≤ Real.log (energyNorm S) := Real.log_nonneg (one_le_energyNorm hS)
    have hM : (0 : ℝ) < maxFan S := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hS))
    have hud : (sharpExponent d : ℝ) ≤ 1 := by exact_mod_cast (sharpExponent_bounds d).2
    by_cases hd1 : d = 1
    · have hmcard := one_dimensional_maxFan_eq_card (hdim.trans hd1) S
      have hl := Real.log_le_log hlam (energyNorm_le_card S)
      rw [hmcard]
      norm_num only [hd1, sharpExponent_one, Rat.cast_one, Nat.cast_one, one_mul, mul_one]
      linarith
    obtain ⟨f, hf, hEf, I, J, hdisj, hcoverEq, hLI, hLJ⟩ := hcut ι S hS
    have hcover : ∀ i, i ∈ I ∨ i ∈ J := by
      intro i
      exact Finset.mem_union.mp (hcoverEq.symm ▸ Finset.mem_univ i)
    have hcard : I.card + J.card = d := by
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hcoverEq, Finset.card_univ, hdim] at hc
      exact hc.symm
    have hw : ∀ x ∈ S, 0 ≤ extendWeight S f x := by
      intro x hx
      simpa only [extendWeight, dif_pos hx] using hf.1 ⟨x, hx⟩
    have hterminal : I = ∅ ∨ J = ∅ →
        (sharpExponent d : ℝ) * Real.log (energyNorm S) - A * d ≤ Real.log (maxFan S) := by
      intro he
      have hn : energyNorm S ≤ Real.exp (B * d) * maxFan S := by
        rcases he with hI | hJ
        · have hJ : J = Finset.univ := by simpa only [hI, Finset.empty_union] using hcoverEq
          rw [hJ, actualMarginalEnergy_univ _ hw, hEf, hdim] at hLJ
          exact hLJ
        · have hI : I = Finset.univ := by simpa only [hJ, Finset.union_empty] using hcoverEq
          rw [hI, actualMarginalEnergy_univ _ hw, hEf, hdim] at hLI
          exact hLI
      have hl := Real.log_le_log hlam hn
      rw [Real.log_mul (Real.exp_ne_zero _) hM.ne', Real.log_exp] at hl
      exact weighted_cut_terminal_scalar (by dsimp [A]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)])
        (Nat.cast_nonneg d) hud hL hl
    by_cases hI0 : I = ∅
    · exact hterminal (Or.inl hI0)
    by_cases hJ0 : J = ∅
    · exact hterminal (Or.inr hJ0)
    have hp : 0 < I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI0)
    have hs : 0 < J.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJ0)
    have hpD : I.card < d := by omega
    have hsD : J.card < d := by omega
    have ha : (0 : ℝ) ≤ sharpExponent I.card := by
      exact_mod_cast (sharpExponent_pos I.card).le
    have hb : (0 : ℝ) ≤ sharpExponent J.card := by
      exact_mod_cast (sharpExponent_pos J.card).le
    have hchild (K : Finset ι) (hK : 0 < K.card) (hKD : K.card < d) :
        ∀ F : Finset (K → ℝ), F.Nonempty →
          Real.exp (-(A * K.card)) * energyNorm F ^ (sharpExponent K.card : ℝ) ≤ (maxFan F : ℝ) := by
      intro F hF
      have hl := ih K.card hKD hK K (by simp) F hF
      have hn := energyNorm_pos hF
      have hm : (0 : ℝ) < maxFan F := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hF))
      apply (Real.log_le_log_iff (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hn _)) hm).mp
      rw [Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos hn _).ne',
        Real.log_exp, Real.log_rpow hn]
      simp only [energyNorm_eq_classical] at hl ⊢
      dsimp only [A]
      linarith
    have hprune := weighted_pruning_log hS hf hEf I J hcover ha hb
      (hchild I hp hpD) (hchild J hs hsD)
    have hposE : 0 < weightedEnergy S (extendWeight S f) := hEf.symm ▸ hlam
    have hLIpos := coordinateMarginalEnergy_pos _ hw hposE I J hcover
    have hLJpos := coordinateMarginalEnergy_pos _ hw hposE J I (fun i ↦ (hcover i).symm)
    rw [coordinateMarginalEnergy_eq_actual _ _ I J hcover] at hLIpos
    rw [coordinateMarginalEnergy_eq_actual _ _ J I (fun i ↦ (hcover i).symm)] at hLJpos
    have hILog := Real.log_le_log hLIpos hLI
    have hJlog := Real.log_le_log hLJpos hLJ
    rw [Real.log_mul (Real.exp_ne_zero _) hM.ne', Real.log_exp, hdim] at hILog hJlog
    have hrec : (sharpExponent d : ℝ) ≤
        ((sharpExponent I.card : ℝ) + sharpExponent J.card) /
          (1 + (sharpExponent I.card : ℝ) + sharpExponent J.card) := by
      have hr := sharpExponent_le_split hp hs
      rw [hcard] at hr
      unfold combineExponent at hr
      exact_mod_cast hr
    apply weighted_cut_induction_scalar (B := B) (A := A) (d := (d : ℝ))
      (p := (I.card : ℝ)) (s := (J.card : ℝ)) rfl
      (by exact_mod_cast hd) (by exact_mod_cast hcard) ha hb hL hrec hILog hJlog
    simpa only [neg_mul] using hprune

end
end Erdos539Geometry
