/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ExposedProjectionBounds
import Erdos539.AxisPalette
import Erdos539.ForbiddenCoverScalar

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance forbiddenExposedMasksDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance forbiddenExposedMasksProjectionDecidableEq
    (S : Finset (ι → ℝ)) (I : Finset ι) : DecidableEq (projection S I) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- The codimension-one numerical cover inequality is derived from the
actual exposed outputs and the actual root optimizer law. -/
theorem codimension_exposed_cover_inequality (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) (hd : 2 ≤ Fintype.card ι)
    (hexposed : ∀ i : ι, IsExposedActiveMask T (Finset.univ.erase i)) :
    (((Fintype.card ι : ℝ) - 2) / (2 * Fintype.card ι) - 3 / (2 * b)) *
      Real.log (energyNorm T) ≤ Real.log (1 + 1 / b) := by
  obtain ⟨f, hfn, hfs, hE⟩ := energyNorm_attained h.nonempty
  have hf : f ∈ admissibleWeights T := ⟨hfn, hfs⟩
  have hl := (energyMaximizer_entropy_bounds h.nonempty hf hE).1
  have hsh := coordinate_codimension_entropy_cover T (fun x ↦ f x ^ 2)
    (fun x ↦ sq_nonneg (f x)) hfs hd
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hW : (0 : ℝ) < (differences T).card := by
    exact_mod_cast (h.nonempty.card_pos.trans_le (card_le_real_differences h.nonempty))
  have hWq := Real.log_le_log hW (show ((differences T).card : ℝ) ≤ ((posDiff T).card : ℝ) ^ 2 by
    exact_mod_cast differences_card_le_posDiff_sq T)
  rw [Real.log_pow] at hWq
  norm_num only [Nat.cast_ofNat] at hWq
  have hpoint (i : ι) : coordinateProjectionEntropy T (fun x ↦ f x ^ 2) (Finset.univ.erase i) ≤
      Real.log (1 + 1 / b) + 3 * Real.log (posDiff T).card - Real.log (energyNorm T) := by
    have hp := (coordinateProjectionEntropy_le_log_card h.nonempty (fun x ↦ f x ^ 2)
      (fun x ↦ sq_nonneg (f x)) hfs (Finset.univ.erase i)).trans
        (h.exposed_projection_log_bound hb (hexposed i))
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hdreal : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < Fintype.card ι := by linarith
  have hL := mul_le_mul_of_nonneg_left hl (show 0 ≤ (Fintype.card ι : ℝ) - 1 by linarith)
  have hc := h.singleton_log_bound hS hb
  have hcm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (3 / 2 : ℝ) * Fintype.card ι by positivity)
  have hlin : ((2 * Fintype.card ι - 1) - (3 / 2 : ℝ) * Fintype.card ι * (1 + 1 / b)) *
      Real.log (energyNorm T) ≤ (Fintype.card ι : ℝ) * Real.log (1 + 1 / b) := by
    nlinarith
  have he : (((Fintype.card ι : ℝ) - 2) / (2 * Fintype.card ι) - 3 / (2 * b)) *
      Fintype.card ι = (2 * Fintype.card ι - 1) - (3 / 2 : ℝ) * Fintype.card ι * (1 + 1 / b) := by
    field_simp
    ring
  rw [← he] at hlin
  nlinarith only [hlin, hdpos]

/-- A full-mask critical core of dimension at least three cannot expose
all codimension-one masks when b >= 4d. All palette and entropy-cover
inputs are proved from the actual critical core and literal exposures. -/
theorem not_all_codimension_masks_exposed
    (h : IsProjectionCriticalCore S b Finset.univ T) (hS : S.Nonempty)
    (hd : 3 ≤ Fintype.card ι) (hb : 4 * (Fintype.card ι : ℝ) ≤ b) :
    ¬ ∀ i : ι, IsExposedActiveMask T (Finset.univ.erase i) := by
  intro hexposed
  have hdreal : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hbpos : 0 < b := by linarith
  have hq : (Fintype.card ι : ℝ) + 1 ≤ (posDiff T).card := by
    exact_mod_cast h.mask_card_add_one_le_palette hbpos
  exact forbidden_codimension_cover_scalar hdreal hb
    (Real.log_nonneg (one_le_energyNorm h.nonempty)) hq
    (h.singleton_log_bound hS hbpos)
    (h.codimension_exposed_cover_inequality hS hbpos (by omega) hexposed)

end IsProjectionCriticalCore
end
end Erdos539Geometry
