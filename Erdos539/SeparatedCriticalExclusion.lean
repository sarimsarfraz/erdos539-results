/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpLeafRetention
import Erdos539.CriticalCoreBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance separatedCriticalDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- A selected core's cardinality deficiency inherits the singleton bound. -/
theorem cardinality_deficiency_bound (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) :
    Real.log T.card - Real.log (energyNorm T) ≤ Real.log (energyNorm T) / b := by
  have hN : (0 : ℝ) < T.card := by exact_mod_cast h.nonempty.card_pos
  have hs := Real.log_le_log hN (by exact_mod_cast card_le_real_posDiff_sq h.nonempty :
    (T.card : ℝ) ≤ ((posDiff T).card : ℝ) ^ 2)
  rw [Real.log_pow] at hs
  have hh := h.singleton_log_bound hS hb
  norm_num only [Nat.cast_ofNat] at hs
  have he : (1 + 1 / b) * Real.log (energyNorm T) =
      Real.log (energyNorm T) + Real.log (energyNorm T) / b := by ring
  rw [he] at hh
  linarith

/-- Fully critical roots admitting a separated hierarchy with terminal
leaf bounds obey the sharp exclusion threshold. Hierarchy existence is
an explicit premise, not a structural claim about arbitrary cores. -/
theorem separated_terminal_log_bound (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) {L : Finset (Finset (ι → ℝ))}
    (hh : SeparatedHierarchy T L) {C : ℝ} (hC : 0 < C)
    (hterminal : ∀ A ∈ L, energyNorm A ≤ C * maxFan A) :
    (1 - (2 * sharpRetentionTau - 1) / b) * Real.log (energyNorm T) ≤ 2 * Real.log C := by
  obtain ⟨A, hA, hret⟩ := hh.exists_leaf_sharp_log_retention
  obtain ⟨hAne, hAT⟩ := hh.leaf_nonempty_subset A hA
  have hdefA := Real.log_le_log (energyNorm_pos hAne) (energyNorm_le_card A)
  have hret' := mul_le_mul_of_nonneg_left hdefA sharpRetentionBeta_pos.le
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hm : (maxFan A : ℝ) ≤ (posDiff T).card := by
    exact_mod_cast (maxFan_mono hAT).trans (maxFan_le_card_posDiff T)
  have hterm := Real.log_le_log (energyNorm_pos hAne)
    ((hterminal A hA).trans (mul_le_mul_of_nonneg_left hm hC.le))
  rw [Real.log_mul hC.ne' hq.ne'] at hterm
  have hroot := h.singleton_log_bound hS hb
  have hdef := mul_le_mul_of_nonneg_left (h.cardinality_deficiency_bound hS hb)
    sharpRetentionBeta_pos.le
  have halg : (1 - (2 * sharpRetentionTau - 1) / b) * Real.log (energyNorm T) =
      2 * Real.log (energyNorm T) -
        (1 + 1 / b) * Real.log (energyNorm T) -
        2 * (sharpRetentionBeta * (Real.log (energyNorm T) / b)) := by
    rw [sharpRetentionTau_eq_beta_add_one]
    ring
  rw [halg]
  linarith

/-- With terminal coefficient one, above the sharp threshold the root
itself has norm one. -/
theorem separated_terminal_one (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) (hthreshold : 2 * sharpRetentionTau - 1 < b)
    {L : Finset (Finset (ι → ℝ))} (hh : SeparatedHierarchy T L)
    (hterminal : ∀ A ∈ L, energyNorm A ≤ maxFan A) : energyNorm T = 1 := by
  have hterm : ∀ A ∈ L, energyNorm A ≤ (1 : ℝ) * maxFan A := by simpa using hterminal
  have hl := h.separated_terminal_log_bound hS hb hh (by norm_num : (0 : ℝ) < 1) hterm
  rw [Real.log_one, mul_zero] at hl
  have hc : 0 < 1 - (2 * sharpRetentionTau - 1) / b := by
    have hh := (div_lt_one hb).mpr hthreshold
    linarith
  have hlog0 := Real.log_nonneg (one_le_energyNorm h.nonempty)
  have hzero : Real.log (energyNorm T) = 0 := by nlinarith
  have he := congrArg Real.exp hzero
  rwa [Real.exp_log (energyNorm_pos h.nonempty), Real.exp_zero] at he

end IsProjectionCriticalCore
end
end Erdos539Geometry
