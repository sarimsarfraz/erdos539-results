/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntervalConstruction
import Erdos539.GluingExactDifferences

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- Every nonnegative interval difference occurs, including zero. -/
theorem intervalVectors_posDiff_card_eq {W : ℕ} (hW : 0 < W) :
    (integerPositiveDifferences (intervalVectors W)).card = W := by
  apply Nat.le_antisymm (intervalVectors_posDiff_card_le W)
  have hsub : intervalVectors W ⊆ integerPositiveDifferences (intervalVectors W) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have h0 : (fun _ : Unit ↦ (0 : ℤ)) ∈ intervalVectors W :=
      Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hW, rfl⟩
    apply mem_integerPositiveDifferences.mpr
    refine ⟨(fun _ : Unit ↦ (t : ℤ)), Finset.mem_image.mpr ⟨t, ht, rfl⟩,
      (fun _ : Unit ↦ (0 : ℤ)), h0, ?_⟩
    funext i
    simp only [intPdiff, sub_zero, max_eq_left (Int.natCast_nonneg t)]
  simpa only [intervalVectors_card] using Finset.card_le_card hsub

/-- The complete interval difference set has exactly 2W-1 elements. -/
theorem intervalVectors_differences_card_eq (W : ℕ) :
    (integerDifferences (intervalVectors W)).card = 2 * W - 1 := by
  classical
  let levels : Finset ℤ := Finset.Icc (1 - (W : ℤ)) ((W : ℤ) - 1)
  let f : ℤ → (Unit → ℤ) := fun g _ ↦ g
  have he : integerDifferences (intervalVectors W) = levels.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerDifferences.mp hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨(t : ℤ) - s, ?_, rfl⟩
      have ht' := Finset.mem_range.mp ht
      have hs' := Finset.mem_range.mp hs
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    · intro hz
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨t, ht, s, hs, hts⟩ := exists_gluing_level_difference hg
      apply mem_integerDifferences.mpr
      refine ⟨(fun _ : Unit ↦ (t : ℤ)), Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩,
        (fun _ : Unit ↦ (s : ℤ)), Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, rfl⟩, ?_⟩
      funext i
      exact hts
  have hf : Function.Injective f := by
    intro g h heq
    exact congrFun heq ()
  rw [he, Finset.card_image_of_injective _ hf]
  dsimp only [levels]
  rw [Int.card_Icc]
  omega

/-- W itself bounds the coordinate diameter, including the empty interval. -/
theorem intervalVectors_diameter (W : ℕ) :
    ∀ x ∈ intervalVectors W, ∀ y ∈ intervalVectors W, ∀ i, |x i - y i| ≤ (W : ℤ) := by
  intro x hx y hy i
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
  have ht' := Finset.mem_range.mp ht
  have hs' := Finset.mem_range.mp hs
  change |(t : ℤ) - s| ≤ (W : ℤ)
  apply abs_le.mpr
  constructor <;> omega

end
end Erdos539Geometry
