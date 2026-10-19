/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyPositiveSupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] in
theorem positiveWeightSupport_zero {S : Finset G} {f : S → ℝ} (hf : ∀ x, 0 ≤ f x)
    {x : G} (hx : x ∈ S) (hnot : x ∉ positiveWeightSupport S f) : extendWeight S f x = 0 := by
  have hle : ¬0 < extendWeight S f x := fun h ↦ hnot (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hnonneg : 0 ≤ extendWeight S f x := by simpa only [extendWeight, dif_pos hx] using hf ⟨x, hx⟩
  exact le_antisymm (le_of_not_gt hle) hnonneg

omit [AddCommGroup G] in
theorem positiveWeightSupport_restriction_pos (S : Finset G) (f : S → ℝ)
    (x : positiveWeightSupport S f) :
    0 < restrictSupportWeight (positiveWeightSupport_subset S f) f x := by
  have h := (Finset.mem_filter.mp x.property).2
  simpa only [extendWeight, dif_pos (positiveWeightSupport_subset S f x.property), restrictSupportWeight] using h

omit [AddCommGroup G] in
theorem positiveWeightSupport_unit {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) :
    ∑ x, restrictSupportWeight (positiveWeightSupport_subset S f) f x ^ 2 = 1 := by
  rw [restrictSupportWeight_squareSum,
    weightSquareSum_support (positiveWeightSupport_subset S f) _ (fun _ hx hn ↦ positiveWeightSupport_zero hf.1 hx hn),
    weightSquareSum_extend, hf.2]

theorem positiveWeightSupport_energy {S : Finset G} {f : S → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    weightedEnergy (positiveWeightSupport S f)
      (extendWeight (positiveWeightSupport S f) (restrictSupportWeight (positiveWeightSupport_subset S f) f)) =
      weightedEnergy S (extendWeight S f) := by
  calc
    _ = weightedEnergy (positiveWeightSupport S f) (extendWeight S f) := by
      apply weightedEnergy_congr
      intro x hx
      exact extend_restrict_mem (positiveWeightSupport_subset S f) f hx
    _ = _ := weightedEnergy_support (positiveWeightSupport_subset S f) _
      (fun _ hx hn ↦ positiveWeightSupport_zero hf hx hn)

end
end Erdos539Geometry
