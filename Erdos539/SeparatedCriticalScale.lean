/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SeparatedCriticalExclusion

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

/-- Exact comparison with the rational intermediate exponent. -/
theorem sharpSidonExponent_lt_thirteen_fifths : sharpSidonExponent < 13 / 5 := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 6 ^ 5)
    (by norm_num : (6 : ℝ) ^ 5 < 2 ^ 13)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  unfold sharpSidonExponent
  apply (div_lt_iff₀ h2).mpr
  linarith

theorem sharpRetentionTau_lt_five_halves : sharpRetentionTau < 5 / 2 := by
  have h := sharpSidonExponent_lt_thirteen_fifths
  unfold sharpRetentionTau
  apply (div_lt_iff₀ (sub_pos.mpr sharpSidonExponent_strict_bounds.2)).mpr
  linarith

variable {ι : Type*} [Fintype ι]
local instance separatedCriticalScaleDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore

/-- With the manuscript's b=4d and terminal cost exp(A d), the logarithmic
root norm is strictly below 4 A d. The dimension is the actual retained mask. -/
theorem separated_terminal_dimension_bound {S T : Finset (ι → ℝ)} {I : Finset ι}
    (h : IsProjectionCriticalCore S (4 * I.card) I T) (hS : S.Nonempty)
    (hd : 2 ≤ I.card) {L : Finset (Finset (ι → ℝ))} (hh : SeparatedHierarchy T L)
    {A : ℝ} (hA : 0 < A)
    (hterminal : ∀ U ∈ L, energyNorm U ≤ Real.exp (A * I.card) * maxFan U) :
    Real.log (energyNorm T) < 4 * A * I.card := by
  have hd' : (2 : ℝ) ≤ I.card := by exact_mod_cast hd
  have hb : (0 : ℝ) < 4 * I.card := by positivity
  have hl := h.separated_terminal_log_bound hS hb hh (Real.exp_pos _) hterminal
  rw [Real.log_exp] at hl
  have hc : (1 / 2 : ℝ) < 1 - (2 * sharpRetentionTau - 1) / (4 * I.card) := by
    have ht := sharpRetentionTau_lt_five_halves
    have hdiv : (2 * sharpRetentionTau - 1) / (4 * I.card) < 1 / 2 := by
      apply (div_lt_iff₀ hb).mpr
      linarith
    linarith
  by_contra hnot
  have hlarge : 4 * A * I.card ≤ Real.log (energyNorm T) := le_of_not_gt hnot
  have hLpos : 0 < Real.log (energyNorm T) := by nlinarith
  have hm := mul_lt_mul_of_pos_right hc hLpos
  nlinarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
