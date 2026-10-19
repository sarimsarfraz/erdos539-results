/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationarySweepLog
import Erdos539.CoordinateProfileExact
import Erdos539.CriticalCoreMarginalEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance parallelProjectionBudgetDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Total actual square-root marginal energy losses are bounded by the
conditional entropy sum, for one fixed exact optimizer. -/
theorem optimizer_parallel_log_loss_le {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    (∑ i, (Real.log (energyNorm S) -
      Real.log (actualMarginalEnergy S (extendWeight S f) (Finset.univ.erase i)))) ≤
      ∑ i, coordinateConditionalEntropy S (fun x ↦ f x ^ 2) i := by
  apply Finset.sum_le_sum
  intro i _
  have h := optimizer_projection_log_energy_lower hS hf hE (Finset.univ.erase i)
  change Real.log (energyNorm S) - coordinateConditionalEntropy S (fun x ↦ f x ^ 2) i ≤ _ at h
  linarith

/-- Full unconditional parallel-loss budget, with the actual maximum fan
and actual square-root marginal energies. This is not a norm upper bound. -/
theorem optimizer_parallel_log_loss_budget {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    (∑ i, (Real.log (energyNorm S) -
      Real.log (actualMarginalEnergy S (extendWeight S f) (Finset.univ.erase i)))) ≤
      Real.log (maxFan S) + 2 * (Fintype.card ι : ℝ) *
        Real.log (finiteEntropy (fun x ↦ f x ^ 2) / Fintype.card ι + 2) +
        3 * (Fintype.card ι : ℝ) := by
  have hs := stationary_sweep_log_bound S (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)) hf.2
  have hcap := stationaryFanCapacity_le_log_maxFan S (fun x ↦ f x ^ 2)
    (fun x ↦ sq_nonneg (f x)) hf.2
  have hl := optimizer_parallel_log_loss_le hS hf hE
  linarith

end
end Erdos539Geometry
