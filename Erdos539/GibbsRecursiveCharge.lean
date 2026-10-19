/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsRecursionBudget

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
local instance recursiveChargeImageDecidableEq (s : GibbsReference G) (φ : G →+ G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

namespace GibbsRecursion

/-- Any verified local charge inequality propagates through the actual
finite sampling law. The local inequality is explicit in this general
lemma; applications below prove it for the concrete geometric charges. -/
theorem expectedCost_le_potential
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (terminal potential : GibbsReference G → ℝ)
    (hterminal : ∀ s, terminal s ≤ potential s)
    (hcut : ∀ s φ, potential (s.image φ) +
      ∑ y, s.sample φ y * (charge s φ y + potential (s.fiber φ y)) ≤ potential s)
    {s : GibbsReference G} (t : GibbsRecursion s) : t.expectedCost charge terminal ≤ potential s := by
  induction t with
  | leaf s => exact hterminal s
  | cut s φ p f ihp ihf =>
    apply le_trans _ (hcut s φ)
    apply add_le_add ihp
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (ihf y)) (s.sample_pos φ y).le

theorem cost_budget_of_local
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (terminal potential : GibbsReference G → ℝ)
    (hterminal : ∀ s, terminal s ≤ potential s)
    (hcut : ∀ s φ, potential (s.image φ) +
      ∑ y, s.sample φ y * (charge s φ y + potential (s.fiber φ y)) ≤ potential s)
    {s : GibbsReference G} (t : GibbsRecursion s) :
    (∑ x, t.probability x * t.cost charge terminal x) ≤ potential s := by
  rw [expectation_cost]
  exact t.expectedCost_le_potential charge terminal potential hterminal hcut

theorem exists_realization_of_local
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (terminal potential : GibbsReference G → ℝ)
    (hterminal : ∀ s, terminal s ≤ potential s)
    (hcut : ∀ s φ, potential (s.image φ) +
      ∑ y, s.sample φ y * (charge s φ y + potential (s.fiber φ y)) ≤ potential s)
    {s : GibbsReference G} (t : GibbsRecursion s) : ∃ x, t.cost charge terminal x ≤ potential s := by
  obtain ⟨x, hx⟩ := exists_le_positive_weighted_average t.probability
    (t.cost charge terminal) t.probability_pos t.probability_sum
  exact ⟨x, hx.trans (t.cost_budget_of_local charge terminal potential hterminal hcut)⟩

end GibbsRecursion
end
end Erdos539Geometry
