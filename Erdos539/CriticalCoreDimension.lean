/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreStructure
import Mathlib.LinearAlgebra.Span.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreDimensionDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Unit coordinate vectors, with exactly the retained original labels. -/
def coreCoordinateUnit {I : Finset ι} (i : I) : I → ℝ := fun j ↦ if j = i then 1 else 0

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

theorem coordinateUnit_mem_difference_span (h : IsProjectionCriticalCore S b I T)
    (hb : 0 < b) (i : I) :
    coreCoordinateUnit i ∈ Submodule.span ℝ (differences (projection T I) : Set (I → ℝ)) := by
  letI : DecidableEq (I → ℝ) := Classical.decEq _
  obtain ⟨x, hx, y, hy, hxy, haxis⟩ := h.axis_pair hb i.property
  have hdiff : project I x - project I y ∈ differences (projection T I) := by
    apply mem_differences.mpr
    refine ⟨project I x, ?_, project I y, ?_, rfl⟩
    · simp only [projection, Finset.mem_image]
      exact ⟨x, hx, rfl⟩
    · simp only [projection, Finset.mem_image]
      exact ⟨y, hy, rfl⟩
  have hu : (x i - y i)⁻¹ • (project I x - project I y) = coreCoordinateUnit i := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.smul_apply, Pi.sub_apply, project, smul_eq_mul, coreCoordinateUnit, if_true]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hxy)
    · have hjval : j.val ≠ i.val := fun he ↦ hji (Subtype.ext he)
      simp only [Pi.smul_apply, Pi.sub_apply, project, smul_eq_mul, coreCoordinateUnit, if_neg hji,
        haxis j.val hjval, sub_self, mul_zero]
  rw [← hu]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hdiff)

/-- The differences of the core span its entire retained coordinate space.
In particular the core has full affine dimension, including the empty mask. -/
theorem projected_difference_span_eq_top (h : IsProjectionCriticalCore S b I T) (hb : 0 < b) :
    Submodule.span ℝ (differences (projection T I) : Set (I → ℝ)) = ⊤ := by
  apply top_unique
  intro x _
  have he : x = ∑ i : I, x i • coreCoordinateUnit i := by
    funext j
    simp [coreCoordinateUnit, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (h.coordinateUnit_mem_difference_span hb i)

end IsProjectionCriticalCore
end
end Erdos539Geometry
