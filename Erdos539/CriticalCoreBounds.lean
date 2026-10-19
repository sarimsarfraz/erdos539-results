/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreSelection
import Erdos539.EnergyPalette

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreBoundsDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The actual positive-difference palette surplus of a finite set. -/
def paletteSurplus (S : Finset (ι → ℝ)) : ℝ := ((posDiff S).card : ℝ) ^ 2 / S.card

omit [Fintype ι] in
theorem paletteSurplus_pos {S : Finset (ι → ℝ)} (hS : S.Nonempty) : 0 < paletteSurplus S := by
  have hq : (0 : ℝ) < (posDiff S).card := by exact_mod_cast posDiff_card_pos hS
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  exact div_pos (pow_pos hq 2) hN

omit [Fintype ι] in
theorem log_paletteSurplus {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    Real.log (paletteSurplus S) = 2 * Real.log (posDiff S).card - Real.log S.card := by
  have hq : (0 : ℝ) < (posDiff S).card := by exact_mod_cast posDiff_card_pos hS
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [paletteSurplus, Real.log_div (pow_pos hq 2).ne' hN.ne', Real.log_pow]
  norm_num

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

theorem log_retention (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty) (hb : 0 < b) :
    Real.log S.card - (2 * b + 1) * Real.log (paletteSurplus S) ≤ Real.log (energyNorm T) := by
  have hsize : Real.log (energyNorm T) ≤ 2 * Real.log (posDiff T).card := by
    have hl := Real.log_le_log (energyNorm_pos h.nonempty) (energyNorm_le_palette_sq h.nonempty)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hl
  apply critical_core_log_retention hb (L0 := Real.log (energyNorm S))
    (Q0 := Real.log (posDiff S).card) (Q := Real.log (posDiff T).card)
  · rw [log_paletteSurplus hS]; ring
  · rw [log_paletteSurplus hS]
    linarith [energyNorm_log_lower_palette hS]
  · exact hsize
  · exact h.compare_parent hS

theorem retention (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty) (hb : 0 < b) :
    (S.card : ℝ) * (paletteSurplus S) ^ (-(2 * b + 1)) ≤ energyNorm T := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hK := paletteSurplus_pos hS
  apply (Real.log_le_log_iff (mul_pos hN (Real.rpow_pos_of_pos hK _)) (energyNorm_pos h.nonempty)).mp
  rw [Real.log_mul hN.ne' (Real.rpow_pos_of_pos hK _).ne', Real.log_rpow hK]
  have hl := h.log_retention hS hb
  linarith

theorem log_surplus (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty) (hb : 0 < b) :
    2 * Real.log (posDiff T).card - Real.log (energyNorm T) ≤
      (2 + 1 / b) * Real.log (paletteSurplus S) := by
  apply critical_core_log_surplus hb (L0 := Real.log (energyNorm S))
    (Q0 := Real.log (posDiff S).card) (X := Real.log S.card)
  · rw [log_paletteSurplus hS]; ring
  · rw [log_paletteSurplus hS]
    linarith [energyNorm_log_lower_palette hS]
  · exact Real.log_le_log (energyNorm_pos h.nonempty)
      ((energyNorm_le_card T).trans (by exact_mod_cast h.card_le))
  · exact h.compare_parent hS

theorem surplus (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty) (hb : 0 < b) :
    ((posDiff T).card : ℝ) ^ 2 / energyNorm T ≤ (paletteSurplus S) ^ (2 + 1 / b) := by
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hnorm := energyNorm_pos h.nonempty
  have hK := paletteSurplus_pos hS
  apply (Real.log_le_log_iff (div_pos (pow_pos hq 2) hnorm) (Real.rpow_pos_of_pos hK _)).mp
  rw [Real.log_div (pow_pos hq 2).ne' hnorm.ne', Real.log_pow, Real.log_rpow hK]
  exact h.log_surplus hS hb

theorem projected_subset_norm_le (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {A : Finset (ι → ℝ)} (hA : A.Nonempty) (hAT : A ⊆ T) {J : Finset ι} (hJI : J ⊆ I) :
    energyNorm (maskedProjection A J) ≤ energyNorm T := by
  have hne := (maskedProjection_nonempty (I := J)).mpr hA
  have hqA : (0 : ℝ) < (posDiff (maskedProjection A J)).card := by
    exact_mod_cast posDiff_card_pos hne
  have hqle : ((posDiff (maskedProjection A J)).card : ℝ) ≤ (posDiff T).card := by
    exact_mod_cast (posDiff_maskedProjection_card_le A J).trans (Finset.card_le_card (posDiff_mono hAT))
  apply (Real.log_le_log_iff (energyNorm_pos hne) (energyNorm_pos h.nonempty)).mp
  exact critical_core_no_log_norm_inflation hb (Real.log_le_log hqA hqle)
    (h.compare_projected_subset hA hAT hJI)

theorem projected_subset_heredity (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {A : Finset (ι → ℝ)} (hA : A.Nonempty) (hAT : A ⊆ T) {J : Finset ι} (hJI : J ⊆ I) :
    ((posDiff T).card : ℝ) *
        (energyNorm (maskedProjection A J) / energyNorm T) ^ criticalAlpha b ≤
      (posDiff (maskedProjection A J)).card := by
  have hne := (maskedProjection_nonempty (I := J)).mpr hA
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hqA : (0 : ℝ) < (posDiff (maskedProjection A J)).card := by
    exact_mod_cast posDiff_card_pos hne
  have hpot := rootPotential_nonneg_of_minimal hb (h.compare_projected_subset hA hAT hJI)
  have hr := rootPotential_inherited hq (energyNorm_pos h.nonempty) hqA (energyNorm_pos hne) hpot
  simpa only [rootPotential_self, neg_zero, Real.exp_zero, one_mul] using hr

theorem singleton_log_bound (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty) (hb : 0 < b) :
    2 * Real.log (posDiff T).card ≤ (1 + 1 / b) * Real.log (energyNorm T) := by
  have hm := h.2.1 (∅, {0}) (singleton_mem_projectionCandidates hS)
  simp only [projectionCandidateScore, criticalLogScore, posDiff_singleton, Finset.card_singleton,
    Nat.cast_one, energyNorm_singleton, Real.log_one, mul_zero, sub_zero] at hm
  exact critical_core_singleton_log_bound hb hm

theorem singleton_bound (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty) (hb : 0 < b) :
    ((posDiff T).card : ℝ) ^ 2 ≤ (energyNorm T) ^ (1 + 1 / b) := by
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hnorm := energyNorm_pos h.nonempty
  apply (Real.log_le_log_iff (pow_pos hq 2) (Real.rpow_pos_of_pos hnorm _)).mp
  rw [Real.log_pow, Real.log_rpow hnorm]
  exact h.singleton_log_bound hS hb

end IsProjectionCriticalCore
end
end Erdos539Geometry
