/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanTranslations

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι κ R : Type*}

def coordinatePad [Zero R] (e : ι ↪ κ) (x : ι → R) : κ → R :=
  Function.extend e x (fun _ ↦ 0)

@[simp] theorem coordinatePad_at [Zero R] (e : ι ↪ κ) (x : ι → R) (i : ι) :
    coordinatePad e x (e i) = x i := e.injective.extend_apply _ _ _

theorem coordinatePad_off [Zero R] (e : ι ↪ κ) (x : ι → R) (j : κ)
    (hj : ¬ ∃ i, e i = j) : coordinatePad e x j = 0 := Function.extend_apply' _ _ _ hj

theorem coordinatePad_injective [Zero R] (e : ι ↪ κ) :
    Function.Injective (coordinatePad (R := R) e) := by
  intro x y h
  funext i
  simpa only [coordinatePad_at] using congrFun h (e i)

def coordinatePadHom [AddZeroClass R] (e : ι ↪ κ) : (ι → R) →+ (κ → R) where
  toFun := coordinatePad e
  map_zero' := by
    funext j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simp
    · simp [coordinatePad_off e _ j hj]
  map_add' x y := by
    funext j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simp
    · simp [coordinatePad_off e _ j hj]

theorem pdiff_coordinatePad (e : ι ↪ κ) (x y : ι → ℝ) :
    pdiff (coordinatePad e x) (coordinatePad e y) = coordinatePad e (pdiff x y) := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [pdiff]
  · simp [pdiff, coordinatePad_off e _ j hj]

theorem fan_coordinatePad [DecidableEq (κ → ℝ)] (e : ι ↪ κ) (F : Finset (ι → ℝ)) (a : ι → ℝ) :
    fan (F.image (coordinatePad e)) (coordinatePad e a) = (fan F a).image (coordinatePad e) := by
  ext z
  simp only [mem_fan, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨pdiff x a, ⟨x, hx, rfl⟩, (pdiff_coordinatePad e x a).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨coordinatePad e x, ⟨x, hx, rfl⟩, pdiff_coordinatePad e x a⟩

theorem maxFan_coordinatePad [DecidableEq (κ → ℝ)] (e : ι ↪ κ) (F : Finset (ι → ℝ)) :
    maxFan (F.image (coordinatePad e)) = maxFan F := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    rw [fan_coordinatePad, Finset.card_image_of_injective _ (coordinatePad_injective e)]
    exact card_fan_le_maxFan hx
  · apply Finset.sup_le
    intro a ha
    have h := card_fan_le_maxFan (Finset.mem_image_of_mem (coordinatePad e) ha)
    rwa [fan_coordinatePad, Finset.card_image_of_injective _ (coordinatePad_injective e)] at h

end
end Erdos539Geometry
