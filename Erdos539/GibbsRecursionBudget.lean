/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsRecursion
import Erdos539.FiniteBranchExpectation

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
local instance recursionBudgetImageDecidableEq (s : GibbsReference G) (φ : G →+ G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

namespace GibbsRecursion

theorem expectation_cost (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (terminal : GibbsReference G → ℝ) {s : GibbsReference G} (t : GibbsRecursion s) :
    (∑ x, t.probability x * t.cost charge terminal x) = t.expectedCost charge terminal := by
  induction t with
  | leaf s => simp [probability, cost, expectedCost, Outcome]
  | cut s φ p f ihp ihf =>
    change (∑ x : p.Outcome × (Σ y, (f y).Outcome),
      (p.probability x.1 * (s.sample φ x.2.1 * (f x.2.1).probability x.2.2)) *
        (p.cost charge terminal x.1 + charge s φ x.2.1 + (f x.2.1).cost charge terminal x.2.2)) = _
    rw [finite_branch_expectation p.probability (s.sample φ) (fun y ↦ (f y).probability)
      p.probability_sum (s.sample_sum φ) (fun y ↦ (f y).probability_sum)
      (p.cost charge terminal) (charge s φ) (fun y ↦ (f y).cost charge terminal), ihp]
    simp_rw [ihf]
    rfl

theorem cost_nonneg (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (terminal : GibbsReference G → ℝ) (hc : ∀ s φ y, 0 ≤ charge s φ y)
    (ht : ∀ s, 0 ≤ terminal s) {s : GibbsReference G} (t : GibbsRecursion s) (x : t.Outcome) :
    0 ≤ t.cost charge terminal x := by
  induction t with
  | leaf s => exact ht s
  | cut s φ p f ihp ihf => exact add_nonneg (add_nonneg (ihp x.1) (hc s φ x.2.1)) (ihf x.2.1 x.2.2)

/-- Telescoping is an equality for the literal recomputed Gibbs cut
charges and all leaf deficits, at arbitrary finite depth. -/
theorem expected_cut_cost {s : GibbsReference G} (t : GibbsRecursion s) :
    t.expectedCost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit = s.deficit := by
  induction t with
  | leaf s => rfl
  | cut s φ p f ihp ihf =>
    simp only [expectedCost, ihp, ihf]
    exact (s.deficit_cut φ).symm

theorem expected_endpoint_cost_le {s : GibbsReference G} (t : GibbsRecursion s) :
    t.expectedCost GibbsReference.endpointCharge GibbsReference.deficit ≤ s.deficit := by
  induction t with
  | leaf s => exact le_rfl
  | cut s φ p f ihp ihf =>
    apply le_trans _ (s.endpointCharge_children_le φ)
    apply add_le_add ihp
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (ihf y)) (s.sample_pos φ y).le

theorem cut_cost_identity {s : GibbsReference G} (t : GibbsRecursion s) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit x) = s.deficit := by
  rw [expectation_cost, expected_cut_cost]

theorem endpoint_cost_budget {s : GibbsReference G} (t : GibbsRecursion s) :
    (∑ x, t.probability x * t.cost GibbsReference.endpointCharge GibbsReference.deficit x) ≤ s.deficit := by
  rw [expectation_cost]
  exact t.expected_endpoint_cost_le

/-- A complete realized tree, retaining both recursive branches at each
cut, costs at most the root deficit. -/
theorem exists_realization_cut_budget {s : GibbsReference G} (t : GibbsRecursion s) :
    ∃ x, t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit x ≤ s.deficit := by
  obtain ⟨x, hx⟩ := exists_le_positive_weighted_average t.probability
    (t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit) t.probability_pos t.probability_sum
  rw [t.cut_cost_identity] at hx
  exact ⟨x, hx⟩

theorem exists_realization_endpoint_budget {s : GibbsReference G} (t : GibbsRecursion s) :
    ∃ x, t.cost GibbsReference.endpointCharge GibbsReference.deficit x ≤ s.deficit := by
  obtain ⟨x, hx⟩ := exists_le_positive_weighted_average t.probability
    (t.cost GibbsReference.endpointCharge GibbsReference.deficit) t.probability_pos t.probability_sum
  exact ⟨x, hx.trans t.endpoint_cost_budget⟩

end GibbsRecursion
end
end Erdos539Geometry
