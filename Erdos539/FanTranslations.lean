/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerTranslations

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι : Type*}

@[simp] theorem translateRealSet_card (F : Finset (ι → ℝ)) (v : ι → ℝ) :
    (translateRealSet F v).card = F.card :=
  Finset.card_image_of_injective _ (add_left_injective v)

theorem fan_translateRealSet (F : Finset (ι → ℝ)) (v a : ι → ℝ) :
    fan (translateRealSet F v) (a + v) = fan F a := by
  unfold fan translateRealSet
  rw [Finset.image_image]
  congr 1
  funext x i
  simp [pdiff]

@[simp] theorem maxFan_translateRealSet (F : Finset (ι → ℝ)) (v : ι → ℝ) :
    maxFan (translateRealSet F v) = maxFan F := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_translateRealSet.mp ha
    rw [fan_translateRealSet]
    exact card_fan_le_maxFan hx
  · apply Finset.sup_le
    intro a ha
    rw [← fan_translateRealSet F v a]
    exact card_fan_le_maxFan (Finset.mem_image_of_mem _ ha)

end
end Erdos539Geometry
