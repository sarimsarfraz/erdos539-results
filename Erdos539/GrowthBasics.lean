/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Factorization
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

theorem card_le_integerDifferences {F : Finset (ι → ℤ)} (hF : F.Nonempty) :
    F.card ≤ (integerDifferences F).card := by
  classical
  obtain ⟨a, ha⟩ := hF
  apply Finset.card_le_card_of_injOn (fun x ↦ x - a)
  · intro x hx
    change x - a ∈ (F ×ˢ F).image (fun p : (ι → ℤ) × (ι → ℤ) ↦ p.1 - p.2)
    exact Finset.mem_image.mpr ⟨(x, a), Finset.mem_product.mpr ⟨hx, ha⟩, rfl⟩
  · intro x _ y _ h
    exact sub_left_injective h

theorem card_le_integerPositiveDifferences_sq {F : Finset (ι → ℤ)} (hF : F.Nonempty) :
    F.card ≤ (integerPositiveDifferences F).card ^ 2 :=
  (card_le_integerDifferences hF).trans (integerDifferences_card_le F)

def growthParameter (n q : ℕ) : ℝ := Real.log (2 * ((q : ℝ) ^ 2 / n))

end
end Erdos539Geometry
