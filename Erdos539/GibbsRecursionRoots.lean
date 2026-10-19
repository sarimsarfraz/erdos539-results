/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsCoordinateExistence
import Erdos539.ReferencePositiveOptimizer
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

namespace GibbsReference

def uniform (S : Finset G) (hS : S.Nonempty) : GibbsReference G where
  support := S
  nonempty := hS
  weight := uniformReference S
  positive := uniformReference_pos hS
  normalized := uniformReference_sum hS

def positiveOptimizer (S : Finset G) (f : S → ℝ) (hf : f ∈ admissibleWeights S) : GibbsReference G where
  support := positiveWeightSupport S f
  nonempty := positiveWeightSupport_nonempty hf
  weight := positiveOptimizerReference S f
  positive := positiveOptimizerReference_pos hf
  normalized := positiveOptimizerReference_sum hf

theorem uniform_deficit_le (S : Finset G) (hS : S.Nonempty) :
    (uniform S hS).deficit ≤ Real.log ((S - S).card / (S.card : ℝ)) :=
  referenceDeficit_uniform_le_log_doubling hS

theorem positiveOptimizer_deficit_le {S : Finset G} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    (positiveOptimizer S f hf).deficit ≤ Real.log ((S.card : ℝ) / energyNorm S) :=
  referenceDeficit_positive_optimizer_le hS hf hE

end GibbsReference

namespace GibbsRecursion

theorem uniform_cut_budget {S : Finset G} (hS : S.Nonempty)
    (t : GibbsRecursion (GibbsReference.uniform S hS)) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit x) ≤
      Real.log ((S - S).card / (S.card : ℝ)) := by
  rw [cut_cost_identity]
  exact GibbsReference.uniform_deficit_le S hS

theorem optimizer_cut_budget {S : Finset G} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (t : GibbsRecursion (GibbsReference.positiveOptimizer S f hf)) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit x) ≤
      Real.log ((S.card : ℝ) / energyNorm S) := by
  rw [cut_cost_identity]
  exact GibbsReference.positiveOptimizer_deficit_le hS hf hE

theorem uniform_endpoint_budget {S : Finset G} (hS : S.Nonempty)
    (t : GibbsRecursion (GibbsReference.uniform S hS)) :
    (∑ x, t.probability x * t.cost GibbsReference.endpointCharge GibbsReference.deficit x) ≤
      Real.log ((S - S).card / (S.card : ℝ)) :=
  t.endpoint_cost_budget.trans (GibbsReference.uniform_deficit_le S hS)

theorem optimizer_endpoint_budget {S : Finset G} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (t : GibbsRecursion (GibbsReference.positiveOptimizer S f hf)) :
    (∑ x, t.probability x * t.cost GibbsReference.endpointCharge GibbsReference.deficit x) ≤
      Real.log ((S.card : ℝ) / energyNorm S) :=
  t.endpoint_cost_budget.trans (GibbsReference.positiveOptimizer_deficit_le hS hf hE)

end GibbsRecursion

section Coordinate
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local instance rootCoordinateDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- An actual complete coordinate recursion and realized tree within the
ordinary difference-doubling budget, for every nonempty finite support. -/
theorem exists_uniform_coordinate_recursion {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    ∃ (t : GibbsRecursion (GibbsReference.uniform S hS)) (x : t.Outcome),
      t.IsCoordinate Finset.univ ∧ t.leafCount x = Fintype.card ι ∧
        t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit x ≤
          Real.log ((S - S).card / (S.card : ℝ)) := by
  have hfixed : (GibbsReference.uniform S hS).FixedOutside Finset.univ := by
    intro _ _ _ _ i hi
    exact (hi (Finset.mem_univ i)).elim
  obtain ⟨t, x, ht, hc, hb⟩ := GibbsRecursion.exists_coordinate_realization_budget
    Finset.univ Finset.univ_nonempty (GibbsReference.uniform S hS) hfixed
  exact ⟨t, x, ht, by simpa only [Finset.card_univ] using hc,
    hb.trans (GibbsReference.uniform_deficit_le S hS)⟩

/-- The complete coordinate recursion starts from every exact optimizer,
including zero atoms, and pays at most the original log(N/Lambda) budget. -/
theorem exists_optimizer_coordinate_recursion {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    ∃ (t : GibbsRecursion (GibbsReference.positiveOptimizer S f hf)) (x : t.Outcome),
      t.IsCoordinate Finset.univ ∧ t.leafCount x = Fintype.card ι ∧
        t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit x ≤
          Real.log ((S.card : ℝ) / energyNorm S) := by
  have hfixed : (GibbsReference.positiveOptimizer S f hf).FixedOutside Finset.univ := by
    intro _ _ _ _ i hi
    exact (hi (Finset.mem_univ i)).elim
  obtain ⟨t, x, ht, hc, hb⟩ := GibbsRecursion.exists_coordinate_realization_budget
    Finset.univ Finset.univ_nonempty (GibbsReference.positiveOptimizer S f hf) hfixed
  exact ⟨t, x, ht, by simpa only [Finset.card_univ] using hc,
    hb.trans (GibbsReference.positiveOptimizer_deficit_le hS hf hE)⟩

end Coordinate
end
end Erdos539Geometry
