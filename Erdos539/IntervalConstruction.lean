/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Gluing

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- An interval, represented as integer vectors in one coordinate. -/
def intervalVectors (W : ℕ) : Finset (Unit → ℤ) :=
  (Finset.range W).image (fun (t : ℕ) _ ↦ (t : ℤ))

@[simp] theorem intervalVectors_card (W : ℕ) : (intervalVectors W).card = W := by
  classical
  have hi : Function.Injective (fun t : ℕ ↦ (fun _ : Unit ↦ (t : ℤ))) := by
    intro t s h
    have he : (t : ℤ) = s := congrFun h ()
    exact_mod_cast he
  rw [intervalVectors, Finset.card_image_of_injective _ hi, Finset.card_range]

theorem intervalVectors_posDiff_card_le (W : ℕ) :
    (integerPositiveDifferences (intervalVectors W)).card ≤ W := by
  classical
  let B : Finset (Unit → ℤ) := (Finset.Ico (0 : ℤ) (W : ℤ)).image (fun t _ ↦ t)
  have hs : integerPositiveDifferences (intervalVectors W) ⊆ B := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerPositiveDifferences.mp hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨max ((t : ℤ) - s) 0, ?_, rfl⟩
    apply Finset.mem_Ico.mpr
    have ht' := Finset.mem_range.mp ht
    have hs' := Finset.mem_range.mp hs
    constructor
    · exact le_max_right _ _
    · omega
  calc
    _ ≤ B.card := Finset.card_le_card hs
    _ ≤ (Finset.Ico (0 : ℤ) (W : ℤ)).card := Finset.card_image_le
    _ = W := by rw [Int.card_Ico]; simp

theorem intervalVectors_differences_card_le (W : ℕ) :
    (integerDifferences (intervalVectors W)).card ≤ 2 * W := by
  classical
  let B : Finset (Unit → ℤ) := (Finset.Icc (1 - (W : ℤ)) ((W : ℤ) - 1)).image (fun t _ ↦ t)
  have hs : integerDifferences (intervalVectors W) ⊆ B := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerDifferences.mp hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨(t : ℤ) - s, ?_, rfl⟩
    apply Finset.mem_Icc.mpr
    have ht' := Finset.mem_range.mp ht
    have hs' := Finset.mem_range.mp hs
    constructor <;> omega
  calc
    _ ≤ B.card := Finset.card_le_card hs
    _ ≤ (Finset.Icc (1 - (W : ℤ)) ((W : ℤ) - 1)).card := Finset.card_image_le
    _ ≤ 2 * W := by rw [Int.card_Icc]; omega

end
end Erdos539Geometry
