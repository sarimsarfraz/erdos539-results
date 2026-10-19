/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductCriticalExclusion

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι κ : Type}
local instance productFactorRealDecidableEq {α : Type} : DecidableEq (α → ℝ) := Classical.decEq _

theorem singleton_factor_palette_ratio {A : Finset (ι → ℝ)} {B : Finset (κ → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) (a : ι → ℝ) :
    ((posDiff (coordinateProduct {a} B)).card : ℝ) / (posDiff (coordinateProduct A B)).card =
      1 / (posDiff A).card := by
  rw [posDiff_coordinateProduct, posDiff_coordinateProduct, coordinateProduct_card,
    coordinateProduct_card, posDiff_singleton, Finset.card_singleton, one_mul, Nat.cast_mul]
  have hqA : (0 : ℝ) < (posDiff A).card := by exact_mod_cast posDiff_card_pos hA
  have hqB : (0 : ℝ) < (posDiff B).card := by exact_mod_cast posDiff_card_pos hB
  field_simp

theorem singleton_factor_norm_ratio {A : Finset (ι → ℝ)} {B : Finset (κ → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) (a : ι → ℝ) :
    energyNorm (coordinateProduct {a} B) / energyNorm (coordinateProduct A B) = 1 / energyNorm A := by
  rw [energyNorm_coordinateProduct, energyNorm_coordinateProduct, energyNorm_singleton, one_mul]
  field_simp [(energyNorm_pos hA).ne', (energyNorm_pos hB).ne']

theorem singleton_factor_violates_palette_retention {A : Finset (ι → ℝ)} {B : Finset (κ → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) (a : ι → ℝ)
    (hlarge : 1 < energyNorm A) (hq : energyNorm A ≤ (posDiff A).card) {θ : ℝ} (hθ : θ < 1) :
    ((posDiff (coordinateProduct {a} B)).card : ℝ) / (posDiff (coordinateProduct A B)).card <
      (energyNorm (coordinateProduct {a} B) / energyNorm (coordinateProduct A B)) ^ θ := by
  rw [singleton_factor_palette_ratio hA hB, singleton_factor_norm_ratio hA hB]
  exact reciprocal_palette_lt_norm_rpow hlarge hq hθ

end
end Erdos539Geometry
