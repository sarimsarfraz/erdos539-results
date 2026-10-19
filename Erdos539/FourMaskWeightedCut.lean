/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourMaskCriticalCut

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance fourMaskWeightedRealDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem weighted_product_le_of_log_bounds {x y M A a c : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hM : 0 < M)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbx : Real.log x ≤ Real.log M + A) (hby : Real.log y ≤ Real.log M + A) :
    x ^ a * y ^ c ≤ Real.exp ((a + c) * A) * M ^ (a + c) := by
  apply (Real.log_le_log_iff
    (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _))
    (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hM _))).mp
  rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hy _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hM _).ne',
    Real.log_rpow hx, Real.log_rpow hy, Real.log_rpow hM, Real.log_exp]
  nlinarith [mul_le_mul_of_nonneg_left hbx ha, mul_le_mul_of_nonneg_left hby hc]

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- Both actual marginal energies and every weighted product are bounded
on each of the same four physical cuts of the same exact root optimizer. -/
theorem four_mask_weighted_cuts (hcrit : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (A : Fin 4 → Finset ι) (c : Fin 4 → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hexposed : ∀ v, IsExposedActiveMask T (A v))
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    (hr : ∑ k, c k ≤ 2) (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hopt : weightedEnergy T (extendWeight T f) = energyNorm T) :
    ∃ J : Fin 4 → Finset ι, ∀ v, J v ⊆ A v ∧ (J v).Nonempty ∧ (Finset.univ \ J v).Nonempty ∧
      Real.log (actualMarginalEnergy T (extendWeight T f) (J v)) ≤
        Real.log (maxFan T) + fourMaskCutAllowance T b (finiteEntropy (fun x ↦ f x ^ 2)) ∧
      Real.log (actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J v)) ≤
        Real.log (maxFan T) + fourMaskCutAllowance T b (finiteEntropy (fun x ↦ f x ^ 2)) ∧
      ∀ a r : ℝ, 0 ≤ a → 0 ≤ r →
        actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J v) ^ a *
          actualMarginalEnergy T (extendWeight T f) (J v) ^ r ≤
            Real.exp ((a + r) * fourMaskCutAllowance T b (finiteEntropy (fun x ↦ f x ^ 2))) *
              (maxFan T : ℝ) ^ (a + r) := by
  obtain ⟨J, hJ⟩ := hcrit.four_mask_projection_cuts hb A c hc hexposed hcover hr hmiss hf hopt
  refine ⟨J, ?_⟩
  intro v
  obtain ⟨hsub, hne, hcne, hlo, hhi⟩ := hJ v
  have hl := (actualMarginal_log_le_projection_card (J v) f hf.2).trans hlo
  have hr := (actualMarginal_log_le_projection_card (Finset.univ \ J v) f hf.2).trans hhi
  refine ⟨hsub, hne, hcne, hl, hr, ?_⟩
  intro a r ha hrr
  apply weighted_product_le_of_log_bounds _ _ _ ha hrr hr hl
  · exact lt_of_lt_of_le zero_lt_one (actualMarginalEnergy_unit_bounds T (Finset.univ \ J v) f hf.2).1
  · exact lt_of_lt_of_le zero_lt_one (actualMarginalEnergy_unit_bounds T (J v) f hf.2).1
  · exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hcrit.nonempty)

end IsProjectionCriticalCore
end
end Erdos539Geometry
