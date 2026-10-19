/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsRecursiveCharge
import Erdos539.GibbsAutocorrelationStability
import Erdos539.GibbsRecursionRoots

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
local instance recursiveStabilityImageDecidableEq (s : GibbsReference G) (φ : G →+ G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

namespace GibbsReference

def alignmentCharge (s : GibbsReference G) (φ : G →+ G) : ℝ :=
  meanImageAutocorrelationDistance s.support φ s.weight s.positive

theorem alignmentCharge_nonneg (s : GibbsReference G) (φ : G →+ G) : 0 ≤ s.alignmentCharge φ :=
  meanImageAutocorrelationDistance_nonneg s.support φ s.weight s.positive

theorem alignmentCharge_le (s : GibbsReference G) (φ : G →+ G) : s.alignmentCharge φ ≤ 12 * s.cutCharge φ := by
  have h := meanImageAutocorrelationDistance_le s.nonempty φ s.weight s.positive
  have hn := projectionReferenceDrift_nonneg s.nonempty φ s.weight s.positive
  unfold alignmentCharge cutCharge
  linarith

theorem alignment_local_budget (s : GibbsReference G) (φ : G →+ G) :
    12 * (s.image φ).deficit +
      ∑ y, s.sample φ y * (s.alignmentCharge φ + 12 * (s.fiber φ y).deficit) ≤ 12 * s.deficit := by
  have h := s.deficit_cut φ
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, s.sample_sum, one_mul] at h ⊢
  have hs : (∑ y, s.sample φ y * (12 * (s.fiber φ y).deficit)) =
      12 * ∑ y, s.sample φ y * (s.fiber φ y).deficit := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hs]
  linarith [s.alignmentCharge_le φ]

def combinedCharge (s : GibbsReference G) (φ : G →+ G) (y : s.support.image φ) : ℝ :=
  s.endpointCharge φ y / 2 + s.alignmentCharge φ / 24

theorem combined_local_budget (s : GibbsReference G) (φ : G →+ G) :
    (s.image φ).deficit +
      ∑ y, s.sample φ y * (s.combinedCharge φ y + (s.fiber φ y).deficit) ≤ s.deficit := by
  have he := s.endpointCharge_children_le φ
  have ha := s.alignment_local_budget φ
  have hid : (s.image φ).deficit +
      (∑ y, s.sample φ y * (s.combinedCharge φ y + (s.fiber φ y).deficit)) =
        ((s.image φ).deficit + ∑ y, s.sample φ y * (s.endpointCharge φ y + (s.fiber φ y).deficit)) / 2 +
        (12 * (s.image φ).deficit + ∑ y, s.sample φ y * (s.alignmentCharge φ + 12 * (s.fiber φ y).deficit)) / 24 := by
    have hsum : (∑ y, s.sample φ y * (s.combinedCharge φ y + (s.fiber φ y).deficit)) =
        ∑ y, (s.sample φ y * (s.endpointCharge φ y + (s.fiber φ y).deficit) / 2 +
          s.sample φ y * (s.alignmentCharge φ + 12 * (s.fiber φ y).deficit) / 24) := by
      apply Finset.sum_congr rfl
      intro y _
      unfold combinedCharge
      ring
    rw [hsum, Finset.sum_add_distrib]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    ring
  rw [hid]
  linarith

end GibbsReference

namespace GibbsRecursion

/-- Expected total alignment over all internal nodes, averaged at each
node over its actual interacting quadruples. -/
theorem alignment_budget {s : GibbsReference G} (t : GibbsRecursion s) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.alignmentCharge φ) (fun _ ↦ 0) x) ≤ 12 * s.deficit :=
  t.cost_budget_of_local _ _ (fun s ↦ 12 * s.deficit)
    (fun s ↦ mul_nonneg (by norm_num) s.deficit_nonneg) GibbsReference.alignment_local_budget

/-- Half the endpoint drift and one twenty-fourth of the alignment cost,
together with all terminal deficits, are paid simultaneously. -/
theorem combined_budget {s : GibbsReference G} (t : GibbsRecursion s) :
    (∑ x, t.probability x * t.cost GibbsReference.combinedCharge GibbsReference.deficit x) ≤ s.deficit :=
  t.cost_budget_of_local _ _ GibbsReference.deficit (fun _ ↦ le_rfl) GibbsReference.combined_local_budget

theorem exists_realization_combined_budget {s : GibbsReference G} (t : GibbsRecursion s) :
    ∃ x, t.cost GibbsReference.combinedCharge GibbsReference.deficit x ≤ s.deficit :=
  t.exists_realization_of_local _ _ GibbsReference.deficit (fun _ ↦ le_rfl) GibbsReference.combined_local_budget

theorem uniform_alignment_budget {S : Finset G} (hS : S.Nonempty)
    (t : GibbsRecursion (GibbsReference.uniform S hS)) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.alignmentCharge φ) (fun _ ↦ 0) x) ≤
      12 * Real.log ((S - S).card / (S.card : ℝ)) :=
  t.alignment_budget.trans (mul_le_mul_of_nonneg_left (GibbsReference.uniform_deficit_le S hS) (by norm_num))

theorem optimizer_alignment_budget {S : Finset G} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (t : GibbsRecursion (GibbsReference.positiveOptimizer S f hf)) :
    (∑ x, t.probability x * t.cost (fun s φ _ ↦ s.alignmentCharge φ) (fun _ ↦ 0) x) ≤
      12 * Real.log ((S.card : ℝ) / energyNorm S) :=
  t.alignment_budget.trans (mul_le_mul_of_nonneg_left (GibbsReference.positiveOptimizer_deficit_le hS hf hE) (by norm_num))

end GibbsRecursion
end
end Erdos539Geometry
