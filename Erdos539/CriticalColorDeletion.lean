/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCorePotential
import Erdos539.CriticalPaletteInversion

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalColorDeletionDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

omit [Fintype ι] in
/-- A collection of actual colors disappears when the vertex set is removed. -/
def KillsColors (B V R : Finset (ι → ℝ)) : Prop :=
  R ⊆ posDiff B ∧ Disjoint R (posDiff (B \ V))

omit [Fintype ι] in
theorem KillsColors.palette_bound {B V R : Finset (ι → ℝ)} (h : KillsColors B V R) :
    ((posDiff (B \ V)).card : ℝ) ≤ (posDiff B).card - R.card := by
  have hsub : R ∪ posDiff (B \ V) ⊆ posDiff B :=
    Finset.union_subset h.1 (posDiff_mono Finset.sdiff_subset)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint h.2] at hc
  have hr : (R.card : ℝ) + (posDiff (B \ V)).card ≤ (posDiff B).card := by exact_mod_cast hc
  linarith

namespace IsProjectionCriticalCore
variable {S T B V R : Finset (ι → ℝ)} {I J : Finset ι} {b : ℝ}

/-- Exact inherited color-deletion certificate. B is a literal nonempty
projected-subset candidate, and f is its own exact optimizer. The empty
remaining support is included. -/
theorem color_deletion_retention (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (hB : (J, B) ∈ projectionCandidates S) (hVB : V ⊆ B) (hkill : KillsColors B V R)
    {f : B → ℝ} (hf : f ∈ admissibleWeights B)
    (hE : weightedEnergy B (extendWeight B f) = energyNorm B) :
    energyNorm B * (1 - weightSquareSum V (extendWeight B f)) ^ 2 ≤
      energyNorm T * (((posDiff B).card - (R.card : ℝ)) / (posDiff T).card) ^ (1 / criticalAlpha b) := by
  have hBne := (mem_projectionCandidates.mp hB).1
  have hα : 0 < criticalAlpha b := by unfold criticalAlpha; positivity
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hpalette := hkill.palette_bound
  have hremaining : 0 ≤ ((posDiff B).card : ℝ) - R.card :=
    (Nat.cast_nonneg (posDiff (B \ V)).card).trans hpalette
  have hnorm : energyNorm (B \ V) ≤
      energyNorm T * (((posDiff B).card - (R.card : ℝ)) / (posDiff T).card) ^ (1 / criticalAlpha b) := by
    by_cases hA : (B \ V).Nonempty
    · have hAc : (J, B \ V) ∈ projectionCandidates S := mem_projectionCandidates.mpr
        ⟨hA, Finset.sdiff_subset.trans (mem_projectionCandidates.mp hB).2⟩
      have hpot := h.candidate_potential_nonneg hb hAc
      have hqA : (0 : ℝ) < (posDiff (B \ V)).card := by exact_mod_cast posDiff_card_pos hA
      apply critical_norm_upper_of_palette hα hq (energyNorm_pos h.nonempty) hqA
        (energyNorm_pos hA) (hqA.trans_le hpalette) hpalette
      unfold rootPotential at hpot
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA, energyNorm_empty]
      exact mul_nonneg (energyNorm_nonneg T) (Real.rpow_nonneg (div_nonneg hremaining hq.le) _)
  have hmass : weightSquareSum (B \ V) (extendWeight B f) =
      1 - weightSquareSum V (extendWeight B f) := by
    have hs := Finset.sum_sdiff (f := fun x ↦ extendWeight B f x ^ 2) hVB
    change weightSquareSum (B \ V) (extendWeight B f) + weightSquareSum V (extendWeight B f) =
      weightSquareSum B (extendWeight B f) at hs
    rw [weightSquareSum_extend, hf.2] at hs
    linarith
  have hret := energyNorm_hereditary (Finset.sdiff_subset : B \ V ⊆ B) hBne hf hE
  rw [hmass] at hret
  exact hret.trans hnorm

end IsProjectionCriticalCore
end
end Erdos539Geometry
