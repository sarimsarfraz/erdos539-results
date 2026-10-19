/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedSliceBound
import Erdos539.EnergyPruning

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance weightedPruningDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Weighted pruning with the actual marginal weights of one fixed parent.
The constants are nonnegative and the exponents are nonnegative; positivity
and normalization of the weight are not strengthened to full support. -/
theorem weighted_pruning {A : Finset (ι → ℝ)} (w : (ι → ℝ) → ℝ)
    (hw : ∀ x ∈ A, 0 ≤ w x) (hE : 0 < weightedEnergy A w)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {cI cJ a b : ℝ} (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → cI * energyNorm F ^ a ≤ (maxFan F : ℝ))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → cJ * energyNorm F ^ b ≤ (maxFan F : ℝ)) :
    cI * cJ * (weightedEnergy A w / (16 * coordinateMarginalEnergy A w J I)) ^ a *
      (weightedEnergy A w / (16 * coordinateMarginalEnergy A w I J)) ^ b ≤ (maxFan A : ℝ) := by
  have hLI := coordinateMarginalEnergy_pos w hw hE I J hcover
  have hLJ := coordinateMarginalEnergy_pos w hw hE J I (fun i ↦ (hcover i).symm)
  have h := energy_aggregate_pruning w hE I J hcover ∅ (Finset.empty_subset _) (Finset.empty_subset _)
    (cI * (weightedEnergy A w / (16 * coordinateMarginalEnergy A w J I)) ^ a)
    (cJ * (weightedEnergy A w / (16 * coordinateMarginalEnergy A w I J)) ^ b)
    (by positivity)
    (fun B hBA hBE ↦ weighted_restricted_fan_lower_bound hBA w hw hE hBE J I
      (fun i ↦ (hcover i).symm) hcI ha hI)
    (fun B hBA hBE ↦ weighted_restricted_fan_lower_bound hBA w hw hE hBE I J hcover hcJ hb hJ)
  rw [maxRestrictedFan_empty] at h
  convert h using 1
  ring

end
end Erdos539Geometry
