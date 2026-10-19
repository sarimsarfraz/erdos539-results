/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinatePadding

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι κ : Type*}

theorem posDiff_translateRealSet (F : Finset (ι → ℝ)) (v : ι → ℝ) :
    posDiff (translateRealSet F v) = posDiff F := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_posDiff.mp hz
    obtain ⟨a, ha, rfl⟩ := mem_translateRealSet.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_translateRealSet.mp hy
    rw [pdiff_translate]
    exact mem_posDiff.mpr ⟨a, ha, b, hb, rfl⟩
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_posDiff.mp hz
    exact mem_posDiff.mpr ⟨a + v, Finset.mem_image_of_mem _ ha,
      b + v, Finset.mem_image_of_mem _ hb, pdiff_translate a b v⟩

theorem posDiff_coordinatePad [DecidableEq (κ → ℝ)] (e : ι ↪ κ) (F : Finset (ι → ℝ)) :
    posDiff (F.image (coordinatePad e)) = (posDiff F).image (coordinatePad e) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_posDiff.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨pdiff a b, mem_posDiff.mpr ⟨a, ha, b, hb, rfl⟩,
      (pdiff_coordinatePad e a b).symm⟩
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_posDiff.mp hw
    exact mem_posDiff.mpr ⟨coordinatePad e a, Finset.mem_image_of_mem _ ha,
      coordinatePad e b, Finset.mem_image_of_mem _ hb, pdiff_coordinatePad e a b⟩

end
end Erdos539Geometry
