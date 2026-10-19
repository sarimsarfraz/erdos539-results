/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreMass
import Erdos539.CriticalCoreDimension
import Erdos539.ProjectionCandidateLift
import Erdos539.CoordinateEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreTheoremDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The quantitative and structural conclusions of the manuscript's full
projection-critical normalization, with the original coordinate labels. -/
structure FullCriticalCore (S : Finset (ι → ℝ)) (b : ℝ) (I : Finset ι)
    (T : Finset (ι → ℝ)) : Prop where
  selected : IsProjectionCriticalCore S b I T
  actual_projected_subset : ∃ A ⊆ S, A.Nonempty ∧ maskedProjection A I = T
  norm_in_actual_coordinates : energyNorm (projection T I) = energyNorm T
  retention : (S.card : ℝ) * paletteSurplus S ^ (-(2 * b + 1)) ≤ energyNorm T
  surplus : ((posDiff T).card : ℝ) ^ 2 / energyNorm T ≤ paletteSurplus S ^ (2 + 1 / b)
  heredity : ∀ {A : Finset (ι → ℝ)}, A.Nonempty → A ⊆ T → ∀ {J : Finset ι}, J ⊆ I →
    ((posDiff T).card : ℝ) * (energyNorm (maskedProjection A J) / energyNorm T) ^ criticalAlpha b ≤
      (posDiff (maskedProjection A J)).card
  no_norm_inflation : ∀ {A : Finset (ι → ℝ)}, A.Nonempty → A ⊆ T → ∀ {J : Finset ι}, J ⊆ I →
    energyNorm (maskedProjection A J) ≤ energyNorm T
  singleton_bound : ((posDiff T).card : ℝ) ^ 2 ≤ energyNorm T ^ (1 + 1 / b)
  full_support : ∀ {f : T → ℝ}, f ∈ admissibleWeights T →
    weightedEnergy T (extendWeight T f) = energyNorm T → ∀ x, 0 < f x
  no_injective_projection : ∀ {J : Finset ι}, J ⊂ I → ¬ Set.InjOn (maskCoordinates J) T
  axis_pairs : ∀ {i : ι}, i ∈ I → ∃ x ∈ T, ∃ y ∈ T, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j
  full_dimension : Submodule.span ℝ (differences (projection T I) : Set (I → ℝ)) = ⊤
  mass_bound : ∀ {f : T → ℝ}, f ∈ admissibleWeights T →
    weightedEnergy T (extendWeight T f) = energyNorm T →
    ∀ {A : Finset (ι → ℝ)}, A.Nonempty → A ⊆ T →
      ((posDiff T).card : ℝ) * weightSquareSum A (extendWeight T f) ^ (1 + 1 / b) ≤ (posDiff A).card
  entropy_defect : ∀ {f : T → ℝ}, f ∈ admissibleWeights T →
    weightedEnergy T (extendWeight T f) = energyNorm T →
      0 ≤ finiteEntropy (fun x : T ↦ f x ^ 2) - Real.log (energyNorm T) ∧
      finiteEntropy (fun x : T ↦ f x ^ 2) - Real.log (energyNorm T) ≤
        (2 + 1 / b) * Real.log (paletteSurplus S)

/-- Full end-to-end normalization. No weighted-cut, quadratic-core, or
regularity hypothesis is assumed. Those are separate proposed bounds. -/
theorem exists_full_projection_critical_core {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {b : ℝ} (hb : 0 < b) : ∃ I T, FullCriticalCore S b I T := by
  obtain ⟨I, T, h⟩ := exists_projectionCriticalCore hS b
  refine ⟨I, T, {
    selected := h
    actual_projected_subset := projectionCandidate_lifts h.1
    norm_in_actual_coordinates := ?_
    retention := h.retention hS hb
    surplus := h.surplus hS hb
    heredity := h.projected_subset_heredity hb
    no_norm_inflation := h.projected_subset_norm_le hb
    singleton_bound := h.singleton_bound hS hb
    full_support := h.optimizer_full_support hb
    no_injective_projection := h.no_injective_proper_projection hb
    axis_pairs := h.axis_pair hb
    full_dimension := h.projected_difference_span_eq_top hb
    mass_bound := h.subset_mass_bound hb
    entropy_defect := h.entropy_defect_bounds hS hb
  }⟩
  exact energyNorm_projection_eq_of_zero_outside
    (fun _ hx _ hi ↦ maskedProjection_zero_outside ((mem_projectionCandidates.mp h.1).2 hx) hi)

end
end Erdos539Geometry
