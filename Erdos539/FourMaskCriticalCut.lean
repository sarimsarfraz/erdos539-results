/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourMaskEntropyCut
import Erdos539.EnergyFanNorm

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance fourMaskCriticalRealDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

def fourMaskCutAllowance (T : Finset (ι → ℝ)) (b H : ℝ) : ℝ :=
  4 * (Real.log (differences T).card - Real.log (energyNorm T)) +
  (3 / 2 : ℝ) * (2 * Real.log (posDiff T).card - Real.log (energyNorm T)) +
  3 * Real.log (1 + 1 / b) - 2 * (H - Real.log (energyNorm T))

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- Every one of four trimmed star cuts controls both literal projection
sizes, with the source's A4 and the entropy saving of the same optimizer. -/
theorem four_mask_projection_cuts (hcrit : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (A : Fin 4 → Finset ι) (c : Fin 4 → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hexposed : ∀ v, IsExposedActiveMask T (A v))
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    (hr : ∑ k, c k ≤ 2) (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hopt : weightedEnergy T (extendWeight T f) = energyNorm T) :
    ∃ J : Fin 4 → Finset ι, ∀ v, J v ⊆ A v ∧ (J v).Nonempty ∧ (Finset.univ \ J v).Nonempty ∧
      Real.log (projection T (J v)).card ≤ Real.log (maxFan T) + fourMaskCutAllowance T b (finiteEntropy (fun x ↦ f x ^ 2)) ∧
      Real.log (projection T (Finset.univ \ J v)).card ≤ Real.log (maxFan T) + fourMaskCutAllowance T b (finiteEntropy (fun x ↦ f x ^ 2)) := by
  let H := finiteEntropy (fun x ↦ f x ^ 2)
  let h := Real.log (1 + 1 / b) + Real.log (posDiff T).card + Real.log (differences T).card - Real.log (energyNorm T)
  obtain ⟨hH, J, hJ⟩ := four_mask_entropy_support_cuts hcrit.nonempty
    (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)) hf.2 A c hc hcover hr hmiss
    (fun v ↦ hcrit.exposed_projection_log_bound hb (hexposed v))
  have hHW : H ≤ Real.log (differences T).card := by
    apply (energyMaximizer_entropy_bounds hcrit.nonempty hf hopt).2.trans
    exact Real.log_le_log (by exact_mod_cast hcrit.nonempty.card_pos : (0 : ℝ) < T.card)
      (by exact_mod_cast card_le_real_differences hcrit.nonempty)
  have hM := Real.log_le_log (energyNorm_pos hcrit.nonempty) (energyNorm_le_maxFan_sq hcrit.nonempty)
  rw [Real.log_pow] at hM
  norm_num only [Nat.cast_ofNat] at hM
  have hbound : 3 * h + Real.log (differences T).card - 2 * H ≤
      Real.log (maxFan T) + fourMaskCutAllowance T b H := by
    dsimp [h, fourMaskCutAllowance]
    linarith
  have hsmall : h ≤ 3 * h + Real.log (differences T).card - 2 * H := by
    change H ≤ 2 * h at hH
    linarith
  refine ⟨J, ?_⟩
  intro v
  obtain ⟨hsub, hne, hcne, hlo, hhi⟩ := hJ v
  exact ⟨hsub, hne, hcne, hlo.trans (hsmall.trans hbound), hhi.trans hbound⟩

/-- The defect-sensitive A4 is bounded by the source's simpler surplus
allowance; exact optimizer nonnegativity of e is used explicitly. -/
theorem four_mask_allowance_le (hcrit : IsProjectionCriticalCore S b I T)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hopt : weightedEnergy T (extendWeight T f) = energyNorm T) :
    fourMaskCutAllowance T b (finiteEntropy (fun x ↦ f x ^ 2)) ≤
      (11 / 2 : ℝ) * (2 * Real.log (posDiff T).card - Real.log (energyNorm T)) + 3 * Real.log (1 + 1 / b) := by
  have hW : (0 : ℝ) < (differences T).card := by
    exact_mod_cast hcrit.nonempty.card_pos.trans_le (card_le_real_differences hcrit.nonempty)
  have hWq := Real.log_le_log hW (show ((differences T).card : ℝ) ≤ ((posDiff T).card : ℝ) ^ 2 by
    exact_mod_cast differences_card_le_posDiff_sq T)
  rw [Real.log_pow] at hWq
  norm_num only [Nat.cast_ofNat] at hWq
  have he := (energyMaximizer_entropy_bounds hcrit.nonempty hf hopt).1
  unfold fourMaskCutAllowance
  linarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
