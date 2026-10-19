/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyImageEquality
import Erdos539.ProductNorm
import Erdos539.ProductFans
import Erdos539.EnergyPalette

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι κ : Type}
local instance coordinateProductRealDecidableEq {α : Type} : DecidableEq (α → ℝ) := Classical.decEq _

def coordinateProductHom : ((ι → ℝ) × (κ → ℝ)) →+ (ι ⊕ κ → ℝ) where
  toFun p := Sum.elim p.1 p.2
  map_zero' := by funext i; cases i <;> rfl
  map_add' _ _ := by funext i; cases i <;> rfl

theorem coordinateProductHom_injective : Function.Injective (coordinateProductHom (ι := ι) (κ := κ)) := by
  intro p q h
  exact Prod.ext (funext (fun i ↦ congrFun h (Sum.inl i))) (funext (fun i ↦ congrFun h (Sum.inr i)))

theorem energyNorm_coordinateProduct (A : Finset (ι → ℝ)) (B : Finset (κ → ℝ)) :
    energyNorm (coordinateProduct A B) = energyNorm A * energyNorm B := by
  change energyNorm ((A ×ˢ B).image coordinateProductHom) = _
  rw [energyNorm_image_of_injective _ _ coordinateProductHom_injective, energyNorm_product]

theorem posDiff_coordinateProduct (A : Finset (ι → ℝ)) (B : Finset (κ → ℝ)) :
    posDiff (coordinateProduct A B) = coordinateProduct (posDiff A) (posDiff B) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_posDiff.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hx
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_coordinateProduct.mp hy
    exact mem_coordinateProduct.mpr ⟨pdiff a c, mem_posDiff.mpr ⟨a, ha, c, hc, rfl⟩,
      pdiff b d, mem_posDiff.mpr ⟨b, hb, d, hd, rfl⟩, (pdiff_sum_elim a c b d).symm⟩
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hz
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_posDiff.mp ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_posDiff.mp hb
    exact mem_posDiff.mpr ⟨Sum.elim a₁ b₁, mem_coordinateProduct.mpr ⟨a₁, ha₁, b₁, hb₁, rfl⟩,
      Sum.elim a₂ b₂, mem_coordinateProduct.mpr ⟨a₂, ha₂, b₂, hb₂, rfl⟩, pdiff_sum_elim a₁ a₂ b₁ b₂⟩

theorem coordinateProduct_mono_left {A A' : Finset (ι → ℝ)} (h : A ⊆ A') (B : Finset (κ → ℝ)) :
    coordinateProduct A B ⊆ coordinateProduct A' B := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hz
  exact mem_coordinateProduct.mpr ⟨a, h ha, b, hb, rfl⟩

theorem coordinateProduct_nonempty {A : Finset (ι → ℝ)} {B : Finset (κ → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) : (coordinateProduct A B).Nonempty :=
  (hA.product hB).image _

end
end Erdos539Geometry
