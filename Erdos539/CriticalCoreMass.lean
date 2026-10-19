/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreStructure

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreMassDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- The maximizing law's mass controls the palette of every nonempty actual
subset of the critical core. The full-support conclusion is not needed. -/
theorem subset_mass_bound (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T)
    {A : Finset (ι → ℝ)} (hA : A.Nonempty) (hAT : A ⊆ T) :
    ((posDiff T).card : ℝ) * (weightSquareSum A (extendWeight T f)) ^ (1 + 1 / b) ≤
      (posDiff A).card := by
  let μ := weightSquareSum A (extendWeight T f)
  have hμ : 0 ≤ μ := weightSquareSum_nonneg A (extendWeight T f)
  have hnorm := energyNorm_pos h.nonempty
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hqA : (0 : ℝ) < (posDiff A).card := by exact_mod_cast posDiff_card_pos hA
  have hpot := rootPotential_nonneg_of_minimal hb (h.compare_subset hA hAT)
  have hbase := rootPotential_inherited hq hnorm hqA (energyNorm_pos hA) hpot
  simp only [rootPotential_self, neg_zero, Real.exp_zero, one_mul] at hbase
  have hretain := energyNorm_hereditary hAT h.nonempty hf hE
  have hratio : μ ^ 2 ≤ energyNorm A / energyNorm T := by
    apply (le_div_iff₀ hnorm).mpr
    simpa only [μ, mul_comm] using hretain
  have hα : 0 ≤ criticalAlpha b := by unfold criticalAlpha; positivity
  have hp := Real.rpow_le_rpow (sq_nonneg μ) hratio hα
  have hexp : (2 : ℝ) * criticalAlpha b = 1 + 1 / b := by
    rw [criticalAlpha_eq hb]
    ring
  have he : (μ ^ 2) ^ criticalAlpha b = μ ^ (1 + 1 / b) := by
    rw [← Real.rpow_natCast μ 2, ← Real.rpow_mul hμ]
    norm_num only [Nat.cast_ofNat]
    rw [hexp]
  rw [he] at hp
  exact (mul_le_mul_of_nonneg_left hp hq.le).trans hbase

end IsProjectionCriticalCore
end
end Erdos539Geometry
