/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Fans

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

def reindexRealVector (e : ι ≃ κ) (x : ι → ℝ) : κ → ℝ := fun i ↦ x (e.symm i)
def reindexRealSet (e : ι ≃ κ) (F : Finset (ι → ℝ)) : Finset (κ → ℝ) :=
  F.image (reindexRealVector e)

@[simp] theorem mem_reindexRealSet {e : ι ≃ κ} {F : Finset (ι → ℝ)} {y : κ → ℝ} :
    y ∈ reindexRealSet e F ↔ ∃ x ∈ F, reindexRealVector e x = y := Finset.mem_image

theorem reindexRealVector_injective (e : ι ≃ κ) : Function.Injective (reindexRealVector e) := by
  intro x y h
  funext i
  have hi := congrFun h (e i)
  simpa only [reindexRealVector, e.symm_apply_apply] using hi

theorem reindexRealSet_card (e : ι ≃ κ) (F : Finset (ι → ℝ)) :
    (reindexRealSet e F).card = F.card := Finset.card_image_of_injective _ (reindexRealVector_injective e)

theorem fan_reindexRealSet (e : ι ≃ κ) (F : Finset (ι → ℝ)) (a : ι → ℝ) :
    fan (reindexRealSet e F) (reindexRealVector e a) = reindexRealSet e (fan F a) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := mem_fan.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_reindexRealSet.mp hy
    exact mem_reindexRealSet.mpr ⟨pdiff x a, mem_fan.mpr ⟨x, hx, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨y, hy, rfl⟩ := mem_reindexRealSet.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_fan.mp hy
    exact mem_fan.mpr ⟨reindexRealVector e x, mem_reindexRealSet.mpr ⟨x, hx, rfl⟩, rfl⟩

theorem maxFan_reindexRealSet (e : ι ≃ κ) (F : Finset (ι → ℝ)) :
    maxFan (reindexRealSet e F) = maxFan F := by
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_reindexRealSet.mp hy
    rw [fan_reindexRealSet, reindexRealSet_card]
    exact card_fan_le_maxFan hx
  · apply Finset.sup_le
    intro x hx
    have h := card_fan_le_maxFan (mem_reindexRealSet.mpr ⟨x, hx, rfl⟩ : reindexRealVector e x ∈ reindexRealSet e F)
    rwa [fan_reindexRealSet, reindexRealSet_card] at h

end
end Erdos539Geometry
