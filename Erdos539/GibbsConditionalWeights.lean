/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsImageFibers
import Erdos539.EnergySupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [DecidableEq G] [DecidableEq H]
local instance gibbsConditionalImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- Conditional 3/4 weights, kept on the original support and zero off
the selected literal fiber. -/
def imageConditionalWeight (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) (x : S) : ℝ :=
  if φ x.val = y.val then (u x / finitePush u (imageEndpoint S φ) y) ^ (3 / 4 : ℝ) else 0

omit [DecidableEq G] in
theorem imageConditionalWeight_nonneg (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (y : S.image φ) (x : S) : 0 ≤ imageConditionalWeight S φ u y x := by
  unfold imageConditionalWeight
  split_ifs
  · exact Real.rpow_nonneg (div_nonneg (hu x).le (finitePush_imageEndpoint_pos S φ u hu y).le) _
  · rfl

omit [DecidableEq G] in
theorem imageConditionalWeight_reconstruct (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (y : S.image φ) (x : S) :
    finitePush u (imageEndpoint S φ) y ^ (3 / 4 : ℝ) * imageConditionalWeight S φ u y x =
      if φ x.val = y.val then referencePowerWeight u x else 0 := by
  have hv := finitePush_imageEndpoint_pos S φ u hu y
  unfold imageConditionalWeight
  split_ifs
  · rw [← Real.mul_rpow hv.le (div_nonneg (hu x).le hv.le)]
    have he : finitePush u (imageEndpoint S φ) y * (u x / finitePush u (imageEndpoint S φ) y) = u x := by
      field_simp
    rw [he]
    rfl
  · rw [mul_zero]

/-- Extension to the root and extension from the actual fiber are the
same ambient weight. -/
theorem extend_imageConditionalWeight (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) :
    extendWeight S (imageConditionalWeight S φ u y) =
      extendWeight (fiber S φ y.val) (referencePowerWeight (imageFiberReference S φ u y)) := by
  funext x
  by_cases hx : x ∈ S
  · by_cases hy : φ x = y.val
    · have hxy := mem_fiber.mpr ⟨hx, hy⟩
      simp only [extendWeight, dif_pos hx, dif_pos hxy, imageConditionalWeight, if_pos hy,
        referencePowerWeight, imageFiberReference, imageFiberEndpoint]
    · have hxy : x ∉ fiber S φ y.val := fun h ↦ hy (mem_fiber.mp h).2
      simp only [extendWeight, dif_pos hx, dif_neg hxy, imageConditionalWeight, if_neg hy]
  · have hxy : x ∉ fiber S φ y.val := fun h ↦ hx (mem_fiber.mp h).1
    simp only [extendWeight, dif_neg hx, dif_neg hxy]

variable [AddCommGroup G]

/-- The conditional energy computed on the root is exactly the new
child's partition function, not the child's ordinary optimized norm. -/
theorem imageConditionalWeight_partition (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) :
    weightedGibbsPartition S (imageConditionalWeight S φ u y) =
      referencePartition (fiber S φ y.val) (imageFiberReference S φ u y) := by
  rw [weightedGibbsPartition, extend_imageConditionalWeight]
  symm
  exact weightedEnergy_support (fun _ hx ↦ (mem_fiber.mp hx).1) _
    (fun _ _ hn ↦ extendWeight_zero_of_not_mem _ _ hn)

end
end Erdos539Geometry
