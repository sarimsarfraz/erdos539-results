/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Fibers
import Erdos539.Factorization
import Erdos539.RealReindex
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset Pointwise Classical
variable {ι κ : Type*}

theorem differences_eq_sub (F : Finset (ι → ℝ)) : differences F = F - F := by
  ext z
  simp only [mem_differences, Finset.mem_sub]

theorem differences_mono {A F : Finset (ι → ℝ)} (hAF : A ⊆ F) :
    differences A ⊆ differences F := by
  rw [differences_eq_sub, differences_eq_sub]
  exact Finset.sub_subset_sub hAF hAF

theorem differences_image_comp (F : Finset (ι → ℝ)) (c : κ → ι) :
    differences (F.image (fun x ↦ x ∘ c)) = (differences F).image (fun x ↦ x ∘ c) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_differences.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨a - b, mem_differences.mpr ⟨a, ha, b, hb, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_differences.mp hv
    exact mem_differences.mpr ⟨a ∘ c, Finset.mem_image_of_mem _ ha,
      b ∘ c, Finset.mem_image_of_mem _ hb, rfl⟩

theorem differences_integerToReal_image (F : Finset (ι → ℤ)) :
    differences (F.image integerToReal) = (integerDifferences F).image integerToReal := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_differences.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨a - b, Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, ?_⟩
    funext i
    simp [integerToReal]
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    refine mem_differences.mpr ⟨integerToReal a, Finset.mem_image_of_mem _ ha,
      integerToReal b, Finset.mem_image_of_mem _ hb, ?_⟩
    funext i
    simp [integerToReal]

theorem differences_integerToReal_image_card (F : Finset (ι → ℤ)) :
    (differences (F.image integerToReal)).card = (integerDifferences F).card := by
  rw [differences_integerToReal_image, integerToReal_image_card]

end
end Erdos539Geometry
