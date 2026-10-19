/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerGeometry

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

/-- Renaming coordinates preserves the integer model exactly. -/
def reindexInteger (e : ι ≃ κ) (x : ι → ℤ) : κ → ℤ := fun j ↦ x (e.symm j)

theorem reindexInteger_injective (e : ι ≃ κ) : Function.Injective (reindexInteger e) := by
  intro x y he
  funext i
  have h := congrFun he (e i)
  simpa only [reindexInteger, Equiv.symm_apply_apply] using h

variable [DecidableEq (κ → ℤ)]

theorem reindexInteger_card (e : ι ≃ κ) (F : Finset (ι → ℤ)) :
    (F.image (reindexInteger e)).card = F.card := by
  classical
  exact Finset.card_image_of_injective _ (reindexInteger_injective e)

theorem integerPositiveDifferences_reindex (e : ι ≃ κ) (F : Finset (ι → ℤ)) :
    integerPositiveDifferences (F.image (reindexInteger e)) =
      (integerPositiveDifferences F).image (reindexInteger e) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerPositiveDifferences.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨intPdiff u v,
      mem_integerPositiveDifferences.mpr ⟨u, hu, v, hv, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerPositiveDifferences.mp hw
    exact mem_integerPositiveDifferences.mpr ⟨reindexInteger e u,
      Finset.mem_image_of_mem _ hu, reindexInteger e v, Finset.mem_image_of_mem _ hv, rfl⟩

theorem integerDifferences_reindex (e : ι ≃ κ) (F : Finset (ι → ℤ)) :
    integerDifferences (F.image (reindexInteger e)) =
      (integerDifferences F).image (reindexInteger e) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerDifferences.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨u - v,
      mem_integerDifferences.mpr ⟨u, hu, v, hv, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerDifferences.mp hw
    exact mem_integerDifferences.mpr ⟨reindexInteger e u,
      Finset.mem_image_of_mem _ hu, reindexInteger e v, Finset.mem_image_of_mem _ hv, rfl⟩

theorem integerPositiveDifferences_reindex_card (e : ι ≃ κ) (F : Finset (ι → ℤ)) :
    (integerPositiveDifferences (F.image (reindexInteger e))).card =
      (integerPositiveDifferences F).card := by
  rw [integerPositiveDifferences_reindex, reindexInteger_card]

theorem integerDifferences_reindex_card (e : ι ≃ κ) (F : Finset (ι → ℤ)) :
    (integerDifferences (F.image (reindexInteger e))).card = (integerDifferences F).card := by
  rw [integerDifferences_reindex, reindexInteger_card]

end
end Erdos539Geometry
