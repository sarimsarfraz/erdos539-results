/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ExposedProjectionBounds
import Erdos539.MaskedCoordinateShearer
import Erdos539.AxisPalette
import Erdos539.ForbiddenCoverScalar

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance criticalMaskedCoverDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance criticalMaskedCoverIndexDecidableEq (I : Finset ι) : DecidableEq I := Classical.decEq _
local instance criticalMaskedCoverProjectionDecidableEq
    (S : Finset (ι → ℝ)) (I : Finset ι) : DecidableEq (projection S I) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- The retained projection of a selected zero-filled core preserves the
whole original law. No change of coordinates or optimizer is made. -/
theorem retained_projection_entropy (h : IsProjectionCriticalCore S b I T) (ν : T → ℝ) :
    coordinateProjectionEntropy T ν I = finiteEntropy ν := by
  apply finiteEntropy_push_eq_of_support_injective
  intro a c _ _ he
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ I
  · exact congrFun (congrArg Subtype.val he) ⟨j, hj⟩
  · rw [maskedProjection_zero_outside ((mem_projectionCandidates.mp h.1).2 a.property) hj,
      maskedProjection_zero_outside ((mem_projectionCandidates.mp h.1).2 c.property) hj]

/-- The codimension-one numerical cover inequality is derived from the
actual exposed outputs and the actual root optimizer law. -/
theorem retained_codimension_exposed_cover_inequality (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) (hd : 2 ≤ I.card)
    (hexposed : ∀ i : I, IsExposedActiveMask T (I.erase i.val)) :
    (((I.card : ℝ) - 2) / (2 * I.card) - 3 / (2 * b)) *
      Real.log (energyNorm T) ≤ Real.log (1 + 1 / b) := by
  obtain ⟨f, hfn, hfs, hE⟩ := energyNorm_attained h.nonempty
  have hf : f ∈ admissibleWeights T := ⟨hfn, hfs⟩
  have hl := (energyMaximizer_entropy_bounds h.nonempty hf hE).1
  have hsh := coordinate_mask_codimension_entropy_cover T (fun x ↦ f x ^ 2)
    (fun x ↦ sq_nonneg (f x)) hfs I hd
  rw [h.retained_projection_entropy] at hsh
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hW : (0 : ℝ) < (differences T).card := by
    exact_mod_cast (h.nonempty.card_pos.trans_le (card_le_real_differences h.nonempty))
  have hWq := Real.log_le_log hW (show ((differences T).card : ℝ) ≤ ((posDiff T).card : ℝ) ^ 2 by
    exact_mod_cast differences_card_le_posDiff_sq T)
  rw [Real.log_pow] at hWq
  norm_num only [Nat.cast_ofNat] at hWq
  have hpoint (i : I) : coordinateProjectionEntropy T (fun x ↦ f x ^ 2) (I.erase i.val) ≤
      Real.log (1 + 1 / b) + 3 * Real.log (posDiff T).card - Real.log (energyNorm T) := by
    have hp := (coordinateProjectionEntropy_le_log_card h.nonempty (fun x ↦ f x ^ 2)
      (fun x ↦ sq_nonneg (f x)) hfs (I.erase i.val)).trans
        (h.exposed_projection_log_bound hb (hexposed i))
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hsum
  have hdreal : (2 : ℝ) ≤ I.card := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < I.card := by linarith
  have hL := mul_le_mul_of_nonneg_left hl (show 0 ≤ (I.card : ℝ) - 1 by linarith)
  have hc := h.singleton_log_bound hS hb
  have hcm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (3 / 2 : ℝ) * I.card by positivity)
  have hlin : ((2 * I.card - 1) - (3 / 2 : ℝ) * I.card * (1 + 1 / b)) *
      Real.log (energyNorm T) ≤ (I.card : ℝ) * Real.log (1 + 1 / b) := by
    nlinarith
  have he : (((I.card : ℝ) - 2) / (2 * I.card) - 3 / (2 * b)) *
      I.card = (2 * I.card - 1) - (3 / 2 : ℝ) * I.card * (1 + 1 / b) := by
    field_simp
    ring
  rw [← he] at hlin
  nlinarith only [hlin, hdpos]

/-- A selected critical core cannot expose every codimension-one mask
of its actual retained coordinates when d >= 3 and b >= 4d. Ambient
zero-filled coordinates and arbitrary original labels are included. -/
theorem not_all_retained_codimension_masks_exposed
    (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty)
    (hd : 3 ≤ I.card) (hb : 4 * (I.card : ℝ) ≤ b) :
    ¬ ∀ i : I, IsExposedActiveMask T (I.erase i.val) := by
  intro hexposed
  have hdreal : (3 : ℝ) ≤ I.card := by exact_mod_cast hd
  have hbpos : 0 < b := by linarith
  have hq : (I.card : ℝ) + 1 ≤ (posDiff T).card := by
    exact_mod_cast h.mask_card_add_one_le_palette hbpos
  exact forbidden_codimension_cover_scalar hdreal hb
    (Real.log_nonneg (one_le_energyNorm h.nonempty)) hq
    (h.singleton_log_bound hS hbpos)
    (h.retained_codimension_exposed_cover_inequality hS hbpos (by omega) hexposed)

end IsProjectionCriticalCore
end
end Erdos539Geometry
