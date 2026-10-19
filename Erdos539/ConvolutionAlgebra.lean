/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyNormalization

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G]

theorem weightedConvolution_comm (S : Finset G) (f g : G → ℝ) (z : G) :
    weightedConvolution S f g z = weightedConvolution S g f z := by
  apply Finset.sum_bij (fun p _ ↦ (p.2, p.1))
  · intro p hp
    obtain ⟨hp, he⟩ := mem_fiber.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact mem_fiber.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by simpa only [add_comm] using he⟩
  · intro p _ q _ he
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro p hp
    obtain ⟨hp, he⟩ := mem_fiber.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact ⟨(p.2, p.1), mem_fiber.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩,
      by simpa only [add_comm] using he⟩, rfl⟩
  · intro p _
    exact mul_comm _ _

theorem weightedConvolution_add_right (S : Finset G) (f g h : G → ℝ) (z : G) :
    weightedConvolution S f (g + h) z = weightedConvolution S f g z + weightedConvolution S f h z := by
  rw [weightedConvolution_comm S f (g + h), weightedConvolution_add_left,
    weightedConvolution_comm S g f, weightedConvolution_comm S h f]

theorem weightedConvolution_scale_left (S : Finset G) (f g : G → ℝ) (c : ℝ) (z : G) :
    weightedConvolution S (fun x ↦ c * f x) g z = c * weightedConvolution S f g z := by
  simpa only [one_mul, mul_one] using weightedConvolution_scale S f g c 1 z

theorem weightedConvolution_scale_right (S : Finset G) (f g : G → ℝ) (c : ℝ) (z : G) :
    weightedConvolution S f (fun x ↦ c * g x) z = c * weightedConvolution S f g z := by
  simpa only [one_mul, mul_one] using weightedConvolution_scale S f g 1 c z

theorem weightedConvolution_variation (S : Finset G) (f g : G → ℝ) (t : ℝ) (z : G) :
    weightedConvolution S (fun x ↦ f x + t * g x) (fun x ↦ f x + t * g x) z =
      weightedConvolution S f f z + 2 * t * weightedConvolution S f g z +
        t ^ 2 * weightedConvolution S g g z := by
  change weightedConvolution S (f + (fun x ↦ t * g x)) (f + (fun x ↦ t * g x)) z = _
  rw [weightedConvolution_add_left, weightedConvolution_add_right,
    weightedConvolution_add_right]
  simp_rw [weightedConvolution_scale_left, weightedConvolution_scale_right]
  rw [weightedConvolution_comm S g f]
  ring

end
end Erdos539Geometry
