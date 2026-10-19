/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinatePartitionTree
import Erdos539.StationaryCountingRoot
import Erdos539.GibbsRecursionRoots

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

namespace StationaryParallelRecursion

theorem counting_depth_weighted_budget {S : Finset G} (hS : S.Nonempty)
    (t : StationaryParallelRecursion (StationaryReferenceState.gibbsRoot (GibbsReference.uniform S hS))) :
    (∑ n, t.reach n * ((1 / 2 : ℝ) ^ (t.depth n + 1) * t.projectionCharge n +
      (1 / 2 : ℝ) ^ t.depth n * t.terminalCharge n)) ≤ Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) := by
  have h := t.gibbs_depth_weighted_budget (GibbsReference.uniform S hS)
  change _ ≤ referenceDeficit S (uniformReference S) at h
  rwa [referenceDeficit_uniform hS] at h

theorem counting_doubling_budget {S : Finset G} (hS : S.Nonempty)
    (t : StationaryParallelRecursion (StationaryReferenceState.gibbsRoot (GibbsReference.uniform S hS))) :
    (∑ n, t.reach n * ((1 / 2 : ℝ) ^ (t.depth n + 1) * t.projectionCharge n +
      (1 / 2 : ℝ) ^ t.depth n * t.terminalCharge n)) ≤ Real.log ((S - S).card / (S.card : ℝ)) :=
  (t.gibbs_depth_weighted_budget (GibbsReference.uniform S hS)).trans (GibbsReference.uniform_deficit_le S hS)

end StationaryParallelRecursion

end
end Erdos539Geometry
