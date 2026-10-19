/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReferenceGibbs
import Erdos539.FiniteConditionalLaws

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [DecidableEq H]
local instance gibbsImageSubtypeDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

def imageEndpoint (S : Finset G) (φ : G → H) (x : S) : S.image φ :=
  ⟨φ x, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩

theorem imageEndpoint_surjective (S : Finset G) (φ : G → H) : Function.Surjective (imageEndpoint S φ) := by
  intro y
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

def imageFiberEndpoint (S : Finset G) (φ : G → H) (y : S.image φ) (x : fiber S φ y.val) : S :=
  ⟨x, (mem_fiber.mp x.property).1⟩

def imageFiberEquiv (S : Finset G) (φ : G → H) (y : S.image φ) :
    {x : S // imageEndpoint S φ x = y} ≃ fiber S φ y.val where
  toFun x := ⟨x.val.val, mem_fiber.mpr ⟨x.val.property, congrArg Subtype.val x.property⟩⟩
  invFun x := ⟨imageFiberEndpoint S φ y x, Subtype.ext (mem_fiber.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finitePush_imageEndpoint_eq_fiber (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) :
    finitePush u (imageEndpoint S φ) y = ∑ x : fiber S φ y.val, u (imageFiberEndpoint S φ y x) := by
  rw [finitePush_eq_sum_fiber]
  apply Fintype.sum_equiv (imageFiberEquiv S φ y)
  intro x
  rfl

theorem finitePush_imageEndpoint_pos (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (y : S.image φ) : 0 < finitePush u (imageEndpoint S φ) y := by
  obtain ⟨x, rfl⟩ := imageEndpoint_surjective S φ y
  exact (hu x).trans_le (le_finitePush u (imageEndpoint S φ) (fun x ↦ (hu x).le) x)

/-- The actual positive conditional reference on a literal nonempty image
fiber, with the original point labels preserved. -/
def imageFiberReference (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ)
    (x : fiber S φ y.val) : ℝ :=
  u (imageFiberEndpoint S φ y x) / finitePush u (imageEndpoint S φ) y

theorem imageFiberReference_pos (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (y : S.image φ) (x : fiber S φ y.val) :
    0 < imageFiberReference S φ u y x :=
  div_pos (hu _) (finitePush_imageEndpoint_pos S φ u hu y)

theorem imageFiberReference_sum (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (y : S.image φ) : ∑ x, imageFiberReference S φ u y x = 1 := by
  simp only [imageFiberReference, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← finitePush_imageEndpoint_eq_fiber]
  exact mul_inv_cancel₀ (finitePush_imageEndpoint_pos S φ u hu y).ne'

theorem imageFiber_nonempty (S : Finset G) (φ : G → H) (y : S.image φ) : (fiber S φ y.val).Nonempty := by
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp y.property
  exact ⟨x, mem_fiber.mpr ⟨hx, he⟩⟩

/-- Disintegration of the carried reference, point by point. -/
theorem imageFiberReference_reconstruct (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (y : S.image φ) (x : fiber S φ y.val) :
    finitePush u (imageEndpoint S φ) y * imageFiberReference S φ u y x = u (imageFiberEndpoint S φ y x) := by
  unfold imageFiberReference
  field_simp [(finitePush_imageEndpoint_pos S φ u hu y).ne']

/-- The conditional definition agrees with the general finite-law
conditional distribution under its explicit actual-fiber equivalence. -/
theorem imageFiberReference_eq_conditional (S : Finset G) (φ : G → H) (u : S → ℝ)
    (y : S.image φ) (x : {x : S // imageEndpoint S φ x = y}) :
    imageFiberReference S φ u y (imageFiberEquiv S φ y x) = conditionalWeight u (imageEndpoint S φ) y x := rfl

variable [AddCommGroup G] [AddCommGroup H]

theorem imageEndpoint_preserves_additive (S : Finset G) (φ : G →+ H) (a b c d : S)
    (he : a.val + b.val = c.val + d.val) :
    (imageEndpoint S φ a).val + (imageEndpoint S φ b).val =
      (imageEndpoint S φ c).val + (imageEndpoint S φ d).val := by
  simpa only [map_add] using congrArg φ he

omit [AddCommGroup H] in
/-- The reference cost is nonnegative at every actual nonempty child. -/
theorem imageFiberReference_deficit_nonneg [DecidableEq G] (S : Finset G) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (y : S.image φ) :
    0 ≤ referenceDeficit (fiber S φ y.val) (imageFiberReference S φ u y) :=
  referenceDeficit_nonneg (imageFiber_nonempty S φ y) (imageFiberReference_pos S φ u hu y)
    (imageFiberReference_sum S φ u hu y)

end
end Erdos539Geometry
