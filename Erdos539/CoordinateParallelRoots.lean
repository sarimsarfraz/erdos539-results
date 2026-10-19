/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateParallelFamilies
import Erdos539.StationaryParallelRoots

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {ι : Type*}
local instance coordinateParallelRootDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace CoordinatePartitionTree

/-- The grouped parallel-family sum starts at the literal ordinary
counting-energy defect for the canonical endpoint and uniform reference. -/
theorem counting_parallel_family_budget {B : Finset ι} (p : CoordinatePartitionTree B)
    {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    let s := StationaryReferenceState.gibbsRoot (GibbsReference.uniform S hS)
    (∑ q : p.Shape, ((1 / 2 : ℝ) ^ (p.shapeDepth q + 1) * p.familyProjection s q +
      (1 / 2 : ℝ) ^ p.shapeDepth q * p.familyTerminal s q)) ≤ Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) := by
  dsimp only
  have h := p.parallel_family_budget (StationaryReferenceState.gibbsRoot (GibbsReference.uniform S hS))
  rw [StationaryReferenceState.gibbsRoot_cost] at h
  change _ ≤ referenceDeficit S (uniformReference S) at h
  rwa [referenceDeficit_uniform hS] at h

theorem counting_parallel_family_doubling {B : Finset ι} (p : CoordinatePartitionTree B)
    {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    let s := StationaryReferenceState.gibbsRoot (GibbsReference.uniform S hS)
    (∑ q : p.Shape, ((1 / 2 : ℝ) ^ (p.shapeDepth q + 1) * p.familyProjection s q +
      (1 / 2 : ℝ) ^ p.shapeDepth q * p.familyTerminal s q)) ≤ Real.log ((S - S).card / (S.card : ℝ)) := by
  dsimp only
  have h := p.parallel_family_budget (StationaryReferenceState.gibbsRoot (GibbsReference.uniform S hS))
  rw [StationaryReferenceState.gibbsRoot_cost] at h
  exact h.trans (GibbsReference.uniform_deficit_le S hS)

/-- For a tree on all coordinates, every actual expanded node is the
complete original fiber outside the block recorded by its tree position. -/
theorem fullOutside_univ [Fintype ι] (p : CoordinatePartitionTree (Finset.univ : Finset ι))
    (s : StationaryReferenceState (ι → ℝ)) (n : (p.realize s).Node) :
    s.FullOutsideFiber ((p.realize s).nodeState n) (p.shapeBlock (p.place s n)) := by
  rw [← p.block_place s n]
  apply p.node_fullOutside_root s _ n
  intro x hx y hy i hi
  exact False.elim (hi (Finset.mem_univ i))

end CoordinatePartitionTree
end
end Erdos539Geometry
