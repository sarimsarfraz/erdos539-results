/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsInterleavedRecursion
import Erdos539.GibbsRecursiveStability

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
local instance interleavedBudgetFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance interleavedBudgetImageDecidableEq (s : GibbsReference G) (φ : G → G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

namespace GibbsInterleavedRecursion

theorem cost_nonneg
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (hc : ∀ s φ y, 0 ≤ charge s φ y) {s : GibbsReference G}
    (t : GibbsInterleavedRecursion s) (x : t.Outcome) : 0 ≤ t.cost charge x := by
  induction t with
  | leaf s => exact s.deficit_nonneg
  | cut s φ p f ihp ihf => exact add_nonneg (add_nonneg (ihp x.1) (hc s φ x.2.1)) (ihf x.2.1 x.2.2)
  | select s n label hsep f ih => exact add_nonneg (s.componentCharge_nonneg label x.1) (ih x.1 x.2)

theorem expectedCost_le_of_local
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (hcut : ∀ s φ, (s.image φ).deficit +
      ∑ y, s.sample φ y * (charge s φ y + (s.fiber φ y).deficit) ≤ s.deficit)
    {s : GibbsReference G} (t : GibbsInterleavedRecursion s) : t.expectedCost charge ≤ s.deficit := by
  induction t with
  | leaf s => exact le_rfl
  | cut s φ p f ihp ihf =>
    apply le_trans _ (hcut s φ)
    apply add_le_add ihp
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (ihf y)) (s.sample_pos φ y).le
  | select s n label hsep f ih =>
    apply le_trans _ (s.component_local_budget label hsep)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (ih i)) (s.componentSample_pos label i).le

theorem budget_of_local
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (hcut : ∀ s φ, (s.image φ).deficit +
      ∑ y, s.sample φ y * (charge s φ y + (s.fiber φ y).deficit) ≤ s.deficit)
    {s : GibbsReference G} (t : GibbsInterleavedRecursion s) :
    (∑ x, t.probability x * t.cost charge x) ≤ s.deficit := by
  rw [expectation_cost]
  exact t.expectedCost_le_of_local charge hcut

/-- Full additive-cut charges and full component-selection charges share
one original reference deficit, with every terminal potential included. -/
theorem cut_budget {s : GibbsReference G} (t : GibbsInterleavedRecursion s) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.cutCharge φ) x) ≤ s.deficit :=
  t.budget_of_local _ (fun s φ ↦ (s.deficit_cut φ).symm.le)

theorem endpoint_budget {s : GibbsReference G} (t : GibbsInterleavedRecursion s) :
    (∑ x, t.probability x * t.cost GibbsReference.endpointCharge x) ≤ s.deficit :=
  t.budget_of_local _ GibbsReference.endpointCharge_children_le

theorem combined_budget {s : GibbsReference G} (t : GibbsInterleavedRecursion s) :
    (∑ x, t.probability x * t.cost GibbsReference.combinedCharge x) ≤ s.deficit :=
  t.budget_of_local _ GibbsReference.combined_local_budget

theorem exists_realization_cut_budget {s : GibbsReference G} (t : GibbsInterleavedRecursion s) :
    ∃ x, t.cost (fun s φ _ ↦ s.cutCharge φ) x ≤ s.deficit := by
  obtain ⟨x, hx⟩ := exists_le_positive_weighted_average t.probability
    (t.cost (fun s φ _ ↦ s.cutCharge φ)) t.probability_pos t.probability_sum
  exact ⟨x, hx.trans t.cut_budget⟩

theorem exists_realization_combined_budget {s : GibbsReference G} (t : GibbsInterleavedRecursion s) :
    ∃ x, t.cost GibbsReference.combinedCharge x ≤ s.deficit := by
  obtain ⟨x, hx⟩ := exists_le_positive_weighted_average t.probability
    (t.cost GibbsReference.combinedCharge) t.probability_pos t.probability_sum
  exact ⟨x, hx.trans t.combined_budget⟩

theorem uniform_cut_budget {S : Finset G} (hS : S.Nonempty)
    (t : GibbsInterleavedRecursion (GibbsReference.uniform S hS)) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.cutCharge φ) x) ≤
      Real.log ((S - S).card / (S.card : ℝ)) :=
  t.cut_budget.trans (GibbsReference.uniform_deficit_le S hS)

theorem optimizer_cut_budget {S : Finset G} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (t : GibbsInterleavedRecursion (GibbsReference.positiveOptimizer S f hf)) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.cutCharge φ) x) ≤
      Real.log ((S.card : ℝ) / energyNorm S) :=
  t.cut_budget.trans (GibbsReference.positiveOptimizer_deficit_le hS hf hE)

end GibbsInterleavedRecursion
end
end Erdos539Geometry
