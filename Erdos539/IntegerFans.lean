/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GluingLayers

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type}

def integerFan (F : Finset (ι → ℤ)) (a : ι → ℤ) : Finset (ι → ℤ) :=
  F.image (fun x ↦ intPdiff x a)

theorem integerToReal_intPdiff (x y : ι → ℤ) :
    integerToReal (intPdiff x y) = pdiff (integerToReal x) (integerToReal y) := by
  funext i
  simp [integerToReal, intPdiff, pdiff]

theorem fan_integerRealSet (F : Finset (ι → ℤ)) (a : ι → ℤ) :
    fan (integerRealSet F) (integerToReal a) = (integerFan F a).image integerToReal := by
  simp only [fan, integerRealSet, integerFan, Finset.image_image]
  congr 1
  funext x
  exact (integerToReal_intPdiff x a).symm

theorem fan_integerRealSet_card (F : Finset (ι → ℤ)) (a : ι → ℤ) :
    (fan (integerRealSet F) (integerToReal a)).card = (integerFan F a).card := by
  rw [fan_integerRealSet, integerToReal_image_card]

theorem integerFan_biUnion_le [DecidableEq (ι → ℤ)] {τ : Type*} (L : Finset τ) (F : τ → Finset (ι → ℤ)) (a : ι → ℤ) :
    (integerFan (L.biUnion F) a).card ≤ ∑ l ∈ L, (integerFan (F l) a).card := by
  have he : integerFan (L.biUnion F) a = L.biUnion (fun l ↦ integerFan (F l) a) := by
    ext z
    simp only [integerFan, Finset.mem_image, Finset.mem_biUnion]
    aesop
  rw [he]
  exact Finset.card_biUnion_le

end
end Erdos539Geometry
