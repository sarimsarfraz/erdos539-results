/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ParallelProjectionBudget

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreProfileCoverDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- The actual maximum fan inherits the singleton comparison. -/
theorem log_maxFan_le_criticalAlpha (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) :
    Real.log (maxFan T) ≤ criticalAlpha b * Real.log (energyNorm T) := by
  have hm : (0 : ℝ) < maxFan T := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan h.nonempty))
  have hlog := Real.log_le_log hm (show (maxFan T : ℝ) ≤ (posDiff T).card by
    exact_mod_cast maxFan_le_card_posDiff T)
  have hs := h.singleton_log_bound hS hb
  have halg : 2 * (criticalAlpha b * Real.log (energyNorm T)) =
      (1 + 1 / b) * Real.log (energyNorm T) := by
    unfold criticalAlpha
    field_simp
  linarith

/-- The manuscript's large-core cover, for the actual selected core and
its canonical optimizer law. The stronger quadratic norm bound is not used. -/
theorem large_core_profile_cover {D : ℕ}
    (h : IsProjectionCriticalCore S (4 * (D : ℝ)) I T)
    (hS : S.Nonempty) (hD : 2 ≤ D) (hd : 2 ≤ Fintype.card ι)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T)
    (hlarge : (48 / 5 : ℝ) * scalarStationaryConstant * Fintype.card ι ≤ Real.log (energyNorm T)) :
    let Q := optimizerStationaryAdditiveLaw h.nonempty hf hE
    (Q.projectLaw Finset.univ).energyProfile ≤
      (∑ i, (Q.projectLaw (Finset.univ.erase i)).energyProfile) / ((Fintype.card ι : ℝ) - 1) := by
  let Q := optimizerStationaryAdditiveLaw h.nonempty hf hE
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hb : (0 : ℝ) < 4 * D := by positivity
  have hL : 0 ≤ Real.log (energyNorm T) := Real.log_nonneg (one_le_energyNorm h.nonempty)
  have hα : criticalAlpha (4 * (D : ℝ)) ≤ 9 / 16 := by
    rw [criticalAlpha_eq hb]
    have hden : (16 : ℝ) ≤ 2 * (4 * D) := by linarith
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hden
    norm_num at hi ⊢
    linarith
  have hfan := h.log_maxFan_le_criticalAlpha hS hb
  have hcap := stationaryFanCapacity_le_log_maxFan T (fun x ↦ f x ^ 2)
    (fun x ↦ sq_nonneg (f x)) hf.2
  have hm := mul_le_mul_of_nonneg_right hα hL
  have hlin := stationary_sweep_linear_bound T (fun x ↦ f x ^ 2)
    (fun x ↦ sq_nonneg (f x)) hf.2
  have hsum : (∑ i, coordinateConditionalEntropy T (fun x ↦ f x ^ 2) i) ≤ Real.log (energyNorm T) := by
    linarith
  have hroot : Q.energyProfile = Real.log (energyNorm T) :=
    optimizerStationaryAdditiveLaw_energyProfile h.nonempty hf hE
  have hid := Q.parallel_profile_identity
  have hcorr : 0 ≤ ∑ i, (Q.correlation - (Q.projectLaw (Finset.univ.erase i)).correlation) :=
    Finset.sum_nonneg (fun i _ ↦ Q.outside_correlation_loss_nonneg i)
  have hden : 0 < (Fintype.card ι : ℝ) - 1 := by
    have hdreal : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
    linarith
  change (Q.projectLaw Finset.univ).energyProfile ≤ _
  rw [Q.projectLaw_univ_energyProfile, le_div_iff₀ hden]
  rw [hroot] at hid ⊢
  nlinarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
