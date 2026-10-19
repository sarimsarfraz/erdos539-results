/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedBinarySet

namespace Erdos539Geometry
noncomputable section
open scoped Classical
local instance selectorRealDecidableEq (d : ℕ) : DecidableEq (Option (Fin d) → ℝ) := Classical.decEq _

/-- Enumerate all 2^d sign choices on the last d coordinates. -/
def selectorSignEnumeration (d : ℕ) : Fin (2 ^ d) ≃ (Fin d → Bool) :=
  Fintype.equivOfCardEq (by simp)

def selectorSigns (d : ℕ) (j : Fin (2 ^ d)) : Option (Fin d) → Bool
  | none => true
  | some i => selectorSignEnumeration d j i

theorem selectorSigns_injective (d : ℕ) : Function.Injective (selectorSigns d) := by
  intro j k he
  apply (selectorSignEnumeration d).injective
  funext i
  exact congrFun he (some i)

/-- A literal integer family in d+1 coordinates, with 2^(2^d) points. -/
def cornerSelectorFamily (d : ℕ) : Finset (Option (Fin d) → ℤ) :=
  signedBinarySet (2 ^ d) (selectorSigns d)

theorem cornerSelectorFamily_dimension (d : ℕ) : Fintype.card (Option (Fin d)) = d + 1 := by simp

theorem cornerSelectorFamily_card (d : ℕ) : (cornerSelectorFamily d).card = 2 ^ (2 ^ d) :=
  signedBinarySet_card (selectorSigns d) none

theorem cornerSelectorFamily_real_card (d : ℕ) :
    (integerRealSet (cornerSelectorFamily d)).card = 2 ^ (2 ^ d) := by
  rw [integerRealSet_card, cornerSelectorFamily_card]

theorem cornerSelectorFamily_boxes (d : ℕ) {a b : Option (Fin d) → ℝ}
    (ha : a ∈ integerRealSet (cornerSelectorFamily d)) (hb : b ∈ integerRealSet (cornerSelectorFamily d)) :
    cornerSlice (integerRealSet (cornerSelectorFamily d)) a b = {a, b} :=
  signedBinarySet_cornerSlice (selectorSigns d) none (fun _ ↦ rfl) (selectorSigns_injective d) ha hb

theorem cornerSelectorFamily_box_card (d : ℕ) {a b : Option (Fin d) → ℝ}
    (ha : a ∈ integerRealSet (cornerSelectorFamily d)) (hb : b ∈ integerRealSet (cornerSelectorFamily d))
    (hab : a ≠ b) : (cornerSlice (integerRealSet (cornerSelectorFamily d)) a b).card = 2 := by
  rw [cornerSelectorFamily_boxes d ha hb, Finset.card_pair hab]

theorem cornerSelectorFamily_maxFan (d : ℕ) :
    maxFan (integerRealSet (cornerSelectorFamily d)) = 2 ^ (2 ^ d) :=
  signedBinarySet_maxFan (selectorSigns d) none

theorem cornerSelectorFamily_box_fraction (d : ℕ) {a b : Option (Fin d) → ℝ}
    (ha : a ∈ integerRealSet (cornerSelectorFamily d)) (hb : b ∈ integerRealSet (cornerSelectorFamily d))
    (hab : a ≠ b) :
    ((cornerSlice (integerRealSet (cornerSelectorFamily d)) a b).card : ℝ) /
      (integerRealSet (cornerSelectorFamily d)).card = (2 : ℝ) / 2 ^ (2 ^ d) := by
  rw [cornerSelectorFamily_box_card d ha hb hab, cornerSelectorFamily_real_card]
  norm_cast

end
end Erdos539Geometry
