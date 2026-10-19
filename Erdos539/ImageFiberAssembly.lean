/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ImageFiberWeights

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [DecidableEq G] [DecidableEq H]
local instance imageAssemblyDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- Assemble arbitrary functions on the disjoint actual image fibers. -/
def imageAssembleWeight (S : Finset G) (φ : G → H)
    (w : (y : S.image φ) → fiber S φ y.val → ℝ) (x : S) : ℝ :=
  ∑ y, extendWeight (fiber S φ y.val) (w y) x.val

theorem imageAssembleWeight_onFiber (S : Finset G) (φ : G → H)
    (w : (y : S.image φ) → fiber S φ y.val → ℝ) (y : S.image φ) (x : fiber S φ y.val) :
    imageAssembleWeight S φ w (imageFiberEndpoint S φ y x) = w y x := by
  unfold imageAssembleWeight
  rw [Finset.sum_eq_single y]
  · simp only [imageFiberEndpoint, extendWeight, dif_pos x.property]
  · intro z _ hzy
    have hn : x.val ∉ fiber S φ z.val := by
      intro hx
      exact hzy (Subtype.ext ((mem_fiber.mp hx).2.symm.trans (mem_fiber.mp x.property).2))
    exact extendWeight_zero_of_not_mem _ _ hn
  · simp

theorem imageFiberWeight_assemble (S : Finset G) (φ : G → H)
    (w : (y : S.image φ) → fiber S φ y.val → ℝ) (y : S.image φ) :
    imageFiberWeight S φ (imageAssembleWeight S φ w) y = w y := by
  funext x
  exact imageAssembleWeight_onFiber S φ w y x

theorem imageAssembleWeight_pos (S : Finset G) (φ : G → H)
    (w : (y : S.image φ) → fiber S φ y.val → ℝ) (hw : ∀ y x, 0 < w y x) (x : S) :
    0 < imageAssembleWeight S φ w x := by
  let y := imageEndpoint S φ x
  let z : fiber S φ y.val := ⟨x.val, mem_fiber.mpr ⟨x.property, rfl⟩⟩
  have he : imageFiberEndpoint S φ y z = x := rfl
  rw [← he, imageAssembleWeight_onFiber]
  exact hw y z

omit [DecidableEq G] in
theorem imageFiber_sum (S : Finset G) (φ : G → H) (g : S → ℝ) :
    (∑ x, g x) = ∑ y : S.image φ, ∑ x : fiber S φ y.val, g (imageFiberEndpoint S φ y x) := by
  rw [← Fintype.sum_fiberwise (imageEndpoint S φ) g]
  apply Finset.sum_congr rfl
  intro y _
  apply Fintype.sum_equiv (imageFiberEquiv S φ y)
  intro x
  rfl

omit [DecidableEq G] in
/-- Actual conditional expectation with the original point labels. -/
theorem imageFiber_expectation (S : Finset G) (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 < ν x) (g : S → ℝ) :
    (∑ x, ν x * g x) = ∑ y, finitePush ν (imageEndpoint S φ) y *
      ∑ x, imageFiberReference S φ ν y x * g (imageFiberEndpoint S φ y x) := by
  rw [imageFiber_sum S φ (fun x ↦ ν x * g x)]
  simp only [Finset.mul_sum, ← mul_assoc, imageFiberReference_reconstruct S φ ν hν]

end
end Erdos539Geometry
