/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourMaskWeightedCut

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance smallCoverAllowanceRealDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

def smallCoverCutAllowance (T : Finset (ι → ℝ)) (b : ℝ) : ℝ :=
  (11 / 2 : ℝ) * (2 * Real.log (posDiff T).card - Real.log (energyNorm T)) + 3 * Real.log (1 + 1 / b)

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

theorem exposed_log_bound_le_small_cover_allowance (hcrit : IsProjectionCriticalCore S b I T) (hb : 0 < b) :
    Real.log (1 + 1 / b) + Real.log (posDiff T).card + Real.log (differences T).card - Real.log (energyNorm T) ≤
      Real.log (maxFan T) + smallCoverCutAllowance T b := by
  have hW : (0 : ℝ) < (differences T).card := by
    exact_mod_cast hcrit.nonempty.card_pos.trans_le (card_le_real_differences hcrit.nonempty)
  have hWq := Real.log_le_log hW (show ((differences T).card : ℝ) ≤ ((posDiff T).card : ℝ) ^ 2 by
    exact_mod_cast differences_card_le_posDiff_sq T)
  have hM := Real.log_le_log (energyNorm_pos hcrit.nonempty) (energyNorm_le_maxFan_sq hcrit.nonempty)
  have hq := Real.log_le_log (energyNorm_pos hcrit.nonempty) (energyNorm_le_palette_sq hcrit.nonempty)
  rw [Real.log_pow] at hWq hM hq
  norm_num only [Nat.cast_ofNat] at hWq hM hq
  have hs : 0 ≤ Real.log (1 + 1 / b) := Real.log_nonneg (by
    have hi : 0 < 1 / b := by positivity
    linarith)
  unfold smallCoverCutAllowance
  linarith

theorem exposed_two_mask_log_cut (hcrit : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {J K : Finset ι} (hJ : IsExposedActiveMask T J) (hK : IsExposedActiveMask T K)
    (hcover : J ∪ K = Finset.univ) (f : T → ℝ) (hf : ∑ x, f x ^ 2 = 1) :
    Real.log (actualMarginalEnergy T (extendWeight T f) J) ≤ Real.log (maxFan T) + smallCoverCutAllowance T b ∧
    Real.log (actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J)) ≤
      Real.log (maxFan T) + smallCoverCutAllowance T b := by
  have hsub : Finset.univ \ J ⊆ K := by
    intro i hi
    have hu : i ∈ J ∪ K := hcover ▸ Finset.mem_univ i
    exact (Finset.mem_union.mp hu).resolve_left (Finset.mem_sdiff.mp hi).2
  have hcard : ((projection T (Finset.univ \ J)).card : ℝ) ≤ (projection T K).card := by
    exact_mod_cast projection_card_mono T hsub
  have hpos : (0 : ℝ) < (projection T (Finset.univ \ J)).card := by
    obtain ⟨x, hx⟩ := hcrit.nonempty
    have hp : (projection T (Finset.univ \ J)).Nonempty :=
      ⟨(projectEndpoint T (Finset.univ \ J) ⟨x, hx⟩).val, (projectEndpoint T (Finset.univ \ J) ⟨x, hx⟩).property⟩
    exact_mod_cast hp.card_pos
  exact ⟨((actualMarginal_log_le_projection_card J f hf).trans
      (hcrit.exposed_projection_log_bound hb hJ)).trans (hcrit.exposed_log_bound_le_small_cover_allowance hb),
    (((actualMarginal_log_le_projection_card (Finset.univ \ J) f hf).trans
      (Real.log_le_log hpos hcard)).trans (hcrit.exposed_projection_log_bound hb hK)).trans
      (hcrit.exposed_log_bound_le_small_cover_allowance hb)⟩

end IsProjectionCriticalCore
end
end Erdos539Geometry
