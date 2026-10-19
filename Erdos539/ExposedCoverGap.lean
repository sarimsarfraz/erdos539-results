/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ExposedProjectionBounds

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem log_norm_bound_of_cover_gap {L B ρ γ : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hγ : 0 < γ) (hρ : ρ ≤ 2 - γ) (h : L ≤ ρ * (L / 2 + B)) :
    L ≤ (4 / γ) * B := by
  have hb := mul_le_mul_of_nonneg_right hρ (show 0 ≤ L / 2 + B by positivity)
  have hγB : 0 ≤ γ * B := mul_nonneg hγ.le hB
  have he : (4 / γ) * B = (4 * B) / γ := by ring
  rw [he]
  apply (le_div_iff₀ hγ).mpr
  nlinarith

variable {ι : Type*} [Fintype ι]
local instance exposedCoverGapDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- An actual exposed fractional cover strictly below weight two bounds
the whole core. Existence of such a cover remains an explicit hypothesis. -/
theorem exposed_cover_gap_bound {κ : Type*} [Fintype κ]
    (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (A : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hexposed : ∀ k, IsExposedActiveMask T (A k))
    (hcover : ∀ i, 1 ≤ ∑ k, if i ∈ A k then c k else 0)
    {γ : ℝ} (hγ : 0 < γ) (hgap : ∑ k, c k ≤ 2 - γ) :
    Real.log (energyNorm T) ≤ (4 / γ) *
      (Real.log (differences T).card - Real.log (energyNorm T) +
        (2 * Real.log (posDiff T).card - Real.log (energyNorm T)) / 2 + Real.log (1 + 1 / b)) := by
  have hL := Real.log_nonneg (one_le_energyNorm h.nonempty)
  have hκ : Real.log (energyNorm T) ≤ Real.log (differences T).card := Real.log_le_log (energyNorm_pos h.nonempty)
    ((energyNorm_le_card T).trans (by exact_mod_cast card_le_real_differences h.nonempty))
  have hδ := Real.log_le_log (energyNorm_pos h.nonempty) (energyNorm_le_palette_sq h.nonempty)
  rw [Real.log_pow] at hδ
  norm_num only [Nat.cast_ofNat] at hδ
  have hs : 0 ≤ Real.log (1 + 1 / b) := Real.log_nonneg (by
    have hp : 0 < 1 / b := by positivity
    linarith)
  apply log_norm_bound_of_cover_gap hL (by linarith) hγ hgap
  have hcvr := h.exposed_fractional_log_bound hb A c hc hexposed hcover
  convert hcvr using 1
  ring

/-- Replacing ordinary difference surplus by palette surplus gives the
source note's simpler bound with coefficient 3/2. -/
theorem exposed_cover_gap_palette_bound {κ : Type*} [Fintype κ]
    (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (A : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hexposed : ∀ k, IsExposedActiveMask T (A k))
    (hcover : ∀ i, 1 ≤ ∑ k, if i ∈ A k then c k else 0)
    {γ : ℝ} (hγ : 0 < γ) (hgap : ∑ k, c k ≤ 2 - γ) :
    Real.log (energyNorm T) ≤ (4 / γ) *
      ((3 / 2 : ℝ) * (2 * Real.log (posDiff T).card - Real.log (energyNorm T)) + Real.log (1 + 1 / b)) := by
  have hmain := h.exposed_cover_gap_bound hb A c hc hexposed hcover hγ hgap
  have hW : (0 : ℝ) < (differences T).card := by
    exact_mod_cast (h.nonempty.card_pos.trans_le (card_le_real_differences h.nonempty))
  have hWq := Real.log_le_log hW (show ((differences T).card : ℝ) ≤ ((posDiff T).card : ℝ) ^ 2 by
    exact_mod_cast differences_card_le_posDiff_sq T)
  rw [Real.log_pow] at hWq
  norm_num only [Nat.cast_ofNat] at hWq
  apply hmain.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4 / γ)
  linarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
